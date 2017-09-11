module project3 where

open import Data.Nat 
open import Data.Bool
open import Data.Vec
open import Data.List hiding (_++_ ; take ; drop ; [_] )
open import Data.Sum
open import Relation.Binary.PropositionalEquality 
open import Data.Product
data Exp   : ℕ → ℕ → Set where

  Truet      : Exp 0 1
  Falset     : Exp 0 1
  And        : Exp 2 1 
  Or         : Exp 2 1
  Not        : Exp 1 1
  Split12    : Exp 1 2
  Split24    : Exp 2 4
  Id         : Exp 1 1
  Swap       : Exp 2 2
  Series     : {i j k : ℕ} → Exp i j → Exp j k → Exp i k
  Parallel   : {i j k l : ℕ} → Exp i j  → Exp k l → Exp (i + k) (j + l)



Nand : Exp 2 1
Nand = Series And Not

Nor : Exp 2 1
Nor = Series Or Not

--pic
Xor : Exp 2 1
Xor = Series (Series Split24 (Parallel Nand Or)) And

--Wiki
Hadder : Exp 2 2
Hadder = Series Split24 (Parallel Xor And)


ABC : Exp 4 1
ABC = Series (Parallel And And) Or

--Gates Using Nor

Not₁ : Exp 1 1
Not₁ = Series Split12 Nor

Or₁ : Exp 2 1
Or₁ = Series (Series Nor Split12) Nor


And₁ : Exp 2 1
And₁ = Series ((Parallel (Series Split12 Nor) (Series Split12 Nor))) Nor

And31 : Exp 3 1
And31 = Series (Parallel And Id) And

--static semantics

data Ctxt : Set where
  □   : Ctxt

data _⊢_      :  ∀{n m : ℕ} → (Γ : Ctxt) → (e :  Exp n m)  → Set where
  TrueT       :  ∀ {Γ} → Γ ⊢ Truet
  FalseT      :  ∀ {Γ} → Γ ⊢ Falset
  AndT        :  ∀ {Γ} → Γ ⊢ And
  OrT         :  ∀ {Γ} → Γ ⊢ Or
  NotT        :  ∀ {Γ} → Γ ⊢ Not
  Split12T    :  ∀ {Γ} → Γ ⊢ Split12
  Split24T    :  ∀ {Γ} → Γ ⊢ Split24
  IdT         :  ∀ {Γ} → Γ ⊢ Id
  SwapT       :  ∀ {Γ} → Γ ⊢ Swap
  SeriesT     :  ∀ {i j k : ℕ} {Γ : Ctxt} {C1 : Exp i j} {C2 : Exp j k} → Γ ⊢ C1  → Γ ⊢ C2 → Γ ⊢ Series C1 C2   
  ParallelT   :  ∀ {i j k l : ℕ} {Γ : Ctxt} {c₁ : Exp i j} { c₂ : Exp k l} → Γ ⊢  c₁  → Γ ⊢ c₂   → Γ ⊢ Parallel  c₁ c₂  

d₁ : □ ⊢ Nand
d₁ = SeriesT AndT NotT


d₂ : □ ⊢ Nor
d₂ = SeriesT OrT NotT

d₃ : □ ⊢ Xor
d₃ = SeriesT (SeriesT Split24T (ParallelT (SeriesT AndT NotT) OrT)) AndT

d₄ :  □ ⊢  Hadder
d₄ = SeriesT Split24T (ParallelT (SeriesT (SeriesT Split24T (ParallelT (SeriesT AndT NotT) OrT)) AndT) AndT)

d₅ :  □ ⊢ ABC
d₅ = SeriesT (ParallelT AndT AndT) OrT


d₆ : □ ⊢ Not₁
d₆ = SeriesT Split12T (SeriesT OrT NotT)

d₇ : □ ⊢ Or₁
d₇ = SeriesT (SeriesT (SeriesT OrT NotT) Split12T) (SeriesT OrT NotT)

d₈ : □ ⊢ Not₁
d₈ = SeriesT Split12T (SeriesT OrT NotT)

--dynamic semantics

Eval :  ∀{i o : ℕ} → Exp i o → Vec Bool i → Vec Bool o
Eval Truet x                        = ( true ∷ [] )
Eval Falset x                       = ( false ∷ [] )
Eval And (x ∷ x₁ ∷ [])              = ( (x ∧ x₁) ∷ [] )
Eval Or (x ∷ x₁ ∷ [])               = ( (x ∨ x₁) ∷ [] )
Eval Not (x ∷  [])                  = ((not x) ∷ [] )
Eval (Series a a₁) x                = ( Eval a₁ (Eval a x))
Eval (Parallel {i}{j}{k}{l} a a₁) x =  (Eval a (take i x))  ++  (Eval a₁ (drop i x))
Eval Split12 (x ∷ [])               = (x ∷ x ∷ [])
Eval Split24  (x ∷ x₁ ∷ [])         = (x ∷ x₁ ∷ x ∷ x₁ ∷ [])
Eval Id (x ∷ [])                    = ( x ∷ [] )
Eval Swap (x ∷ x₁ ∷ [])             = (x₁ ∷ x ∷ [])

test1 : ∀ {t} (b : Bool) → Eval And (false ∷ ( b ∷ [])) ≡ t → t ≡ ( false  ∷ [])
test1 x b = sym b

test2 : ∀ {t} (b : Bool) → Eval Or (true ∷ ( b ∷ [])) ≡ t → t ≡ ( true  ∷ [])
test2 b x =  sym x

test3 : ∀ {t} → Eval Not  ( false ∷ []) ≡ t → t ≡ (true ∷ [])
test3 x =  sym x

test4 : ∀ {t} → Eval Not  ( true ∷ []) ≡ t → t ≡ (false ∷ [])
test4 x =  sym x

test5 : ∀ {t} → Eval Not₁  ( true ∷ []) ≡ t → t ≡ (false ∷ [])
test5 x =  sym x

test7 : ∀ {t}  → Eval Hadder  (true   ∷ (false   ∷ [])) ≡ t  → t ≡ (true  ∷ (false   ∷ []))
test7 a = sym a

test8 : ∀ {t}  → Eval Hadder  (true   ∷ (true   ∷ [])) ≡ t  → t ≡ (false  ∷ (true  ∷ []))
test8 a = sym a

test9 : ∀ {t} → Eval Xor  (false   ∷ (false   ∷ [])) ≡ t  → t ≡  (false   ∷ [])
test9 x =   sym x


test6 : ∀ {t t₁ } (a : Bool) → Eval Not  ( a  ∷ []) ≡ t  → Eval Not₁ ( a  ∷ []) ≡ t₁  → t ≡ t₁
test6 true  refl refl = refl
test6 false refl refl = refl


test10 : ∀ {t t₁ } {a b : Bool} → Eval Or  (a   ∷ (b   ∷ [])) ≡ t → Eval Or₁  (a   ∷ (b   ∷ [])) ≡ t₁  → t ≡  t₁
test10 {true ∷ []} {true ∷ []} p1 p2 = refl
test10 {true ∷ []} {false ∷ []} p1 p2 = {!!}
test10 {false ∷ []} {true ∷ []} p1 p2 = {!!}
test10 {false ∷ []} {false ∷ []} p1 p2 = refl


test11 : ∀ {t t₁ } {a b : Bool} → Eval And  (a   ∷ (b   ∷ [])) ≡ t → Eval And₁  (a   ∷ (b   ∷ [])) ≡ t₁  → t ≡  t₁
test11 {true ∷ []} {true ∷ []} p1 p2 = refl
test11 {true ∷ []} {false ∷ []} p1 p2 = {!!}
test11 {false ∷ []} {true ∷ []} p1 p2 = {!!}
test11 {false ∷ []} {false ∷ []} p1 p2 = refl












data Frame   : ℕ → ℕ → Set where
  SeriesK    : ∀ {n m : ℕ} → (e : Exp n m) → Frame n m
  ParallelLK : ∀ {n m k : ℕ} → (Vec Bool n) → (e : Exp n m) → Frame k (k + m)
  ParallelRK : ∀ {n m : ℕ} → (Vec Bool n) → Frame m (n + m)

data Cont : ℕ → ℕ → Set where
  mtK   : ∀ {i j : ℕ} → Cont i j
  consK : ∀ {i j k : ℕ} → Frame i j → Cont j k → Cont i k 

data ⊢f_ : ∀ {m n} → Frame m n → Set where
  frame : ∀ {m n} → (f : Frame m n) → ⊢f f

data ⊢k_ : ∀ {m n} → Cont m n → Set where
  mtKT : ∀ {n m} → (mtK : Cont n m) → ⊢k mtK
  consKT : ∀ {a b c} {f : Frame a b} {k : Cont b c} → ⊢f f → ⊢k k → ⊢k (consK f k)

data State : Set where
  Enter : ∀ {n m o : ℕ} → Exp n m → Vec Bool n → Cont m o → State
  Return : ∀ {n m : ℕ} → Vec Bool n → Cont n m → State 

data Step : State → State → Set where
  trueE : ∀ {m} {k : Cont 1 m} →
          Step (Enter  Truet [] k)
               (Return Data.Vec.[ true ] k)
  falseE : ∀ {m} {k : Cont 1 m} →
           Step (Enter Falset [] k)
                (Return Data.Vec.[ false ] k)
  andE   : ∀ {m} {b1 b2} {k : Cont 1 m} →
           Step (Enter And (b1 ∷ (b2 ∷ [])) k)
                (Return Data.Vec.[ b1 ∧ b2 ] k)
  orE    : ∀ {m} {b1 b2} {k : Cont 1 m} →
           Step (Enter Or ( b1 ∷ b2 ∷ []) k)
                (Return Data.Vec.[ b1 ∨ b2 ] k)
  notE    : ∀ {m} {b} {k : Cont 1 m} →
            Step (Enter Not Data.Vec.[ b ] k)
                 (Return Data.Vec.[ not b ] k) 
  splitE  : ∀ {m} {b} {k : Cont 2 m} →
             Step (Enter Split12 (b ∷ []) k)
                  (Return (b ∷ b ∷ []) k)
  idE     : ∀ {m} {b} {k : Cont 1 m} →
            Step (Enter Id Data.Vec.[ b ] k)
                 (Return Data.Vec.[ b ] k)
  swapE    : ∀ {m} {b1 b2} {k : Cont 2 m} →
              Step (Enter Swap (b1 ∷ b2 ∷ []) k)
                   (Return (b2 ∷ b1 ∷ []) k)
  seriesE    : ∀ {i j m l} {c1 : Exp i j} {c2 : Exp j m} {input : Vec Bool i} {k : Cont m l} →
               Step (Enter (Series c1 c2) input k)
                    (Enter c1 input (consK (SeriesK c2) k))
  seriesR  : ∀ {i j m} {output : Vec Bool i} {c : Exp i j} {k : Cont j m} →
             Step (Return output (consK (SeriesK c) k))
                  (Enter c output k)
  paraE    : ∀ {a b c d m} {c1 : Exp a b} {c2 : Exp c d} {input : Vec Bool (a + c)} {k : Cont (b + d) m} →
             Step (Enter (Parallel c1 c2) input k)
                  (Enter c1 (take a input) (consK (ParallelLK (drop a input) c2) k))
  paraR1  : ∀ {i j l m} {output : Vec Bool i} {ins : Vec Bool j} {c : Exp j l} {k : Cont (i + l) m} →
            Step (Return output (consK (ParallelLK ins c) k))
                 (Enter c ins (consK (ParallelRK output) k))

data Step* : State → State → Set where
  ∎ : ∀ {s} → Step* s s 
  _•_ : ∀ {s₁ s₂ s₃} → Step s₁ s₂ → Step* s₂ s₃ → Step* s₁ s₃

ex1 : Step* (Enter (Series Or (Series Split12 And)) ( false ∷ true ∷ [] ) mtK)
            (Return (true ∷ []) mtK)
ex1 = seriesE • (orE • (seriesR • (seriesE • (splitE • (seriesR • (andE • ∎))))))
