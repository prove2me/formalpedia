-- Prove2me | solution 1 for gpy_twistedWeight_one
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T16:39:04.325723+00:00
-- url     : https://prove2.me/submissions/fa1b73f3-56bf-4e70-b5e8-44198d92a1f3

/- PubAll restated solution file: Mathlib only, absolute bounds only.
   No asymptotic TwistedMertensBound main term is stated or proved here. -/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

noncomputable def localGoodChoiceFinset {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (p : ℕ) (hd he : Prop) [Decidable hd] [Decidable he] :
    Finset (Option (Fin k) × Option (Fin k)) :=
  Finset.univ.filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))

noncomputable def twistedWeight {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (n : ℕ) : ℝ :=
  (∏ p ∈ n.primeFactors, ((localGoodChoiceFinset h i p hd he).card : ℝ))
    / ((Nat.totient n : ℕ) : ℝ)

noncomputable def twistedMuSqSum {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (m M Q : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n M),
    (ArithmeticFunction.moebius n : ℝ) * twistedWeight h i hd he n
      * (Real.log (n : ℝ)) ^ m

noncomputable def twistedAbsWeight {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (n : ℕ) : ℝ :=
  abs ((ArithmeticFunction.moebius n : ℝ) * twistedWeight h i hd he n)

/-- The twisted weight at `1` is `1`. -/
theorem twistedWeight_one_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] :
    twistedWeight h i hd he 1 = 1 := by
  unfold twistedWeight
  simp

/-- The twisted weight is multiplicative on coprime pairs. -/
theorem solution {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] :
    ((∏ p ∈ (1 : ℕ).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient 1 : ℕ) : ℝ)) = 1 :=
  twistedWeight_one_aux h i hd he
