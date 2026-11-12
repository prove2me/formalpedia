-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_generic_nat_family_independent_of_atomic_product
-- name    : AvramDividend.Classical.avram_a06_generic_nat_family_independent_of_atomic_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:16:37.932245+00:00
-- url     : https://prove2.me/theorems/f6aa4657-5ea9-4985-9492-1eee95f1ea85
-- title:
--   Atomic joint product probabilities imply independence of a finite measurable natural-number family
-- statement:
--   A finite family of measurable natural-valued random variables is independent when every full vector of singleton events has the product probability. The proof is discrete measure uniqueness and extends atomic factorisation to measurable product cylinders; it needs no exponential renewal assumptions.

import Mathlib
open MeasureTheory ProbabilityTheory Set Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_generic_nat_family_independent_of_atomic_product
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Z : Fin n → Ω → ℕ)
    (hZ : ∀ i, Measurable (Z i))
    (hAtoms : ∀ v : Fin n → ℕ,
      P {ω | ∀ i, Z i ω = v i} =
        ∏ i : Fin n, P {ω | Z i ω = v i}) :
    iIndepFun Z P := by sorry
