-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_generic_finite_nat_atomic_chain_product
-- name    : AvramDividend.Classical.avram_a06_generic_finite_nat_atomic_chain_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:31:03.785831+00:00
-- url     : https://prove2.me/theorems/7a968b01-a3f6-42e6-8775-54d81e949794
-- title:
--   Finite one-step atomic factorisation telescopes to a full product law
-- statement:
--   For a finite family of natural-valued random variables, if the next coordinate's singleton event is independent of each specified cylinder of all preceding coordinates, then repeated multiplication gives every joint singleton cylinder probability as the product of marginal probabilities. This is a pure finite induction and contains no original renewal driver.

import Mathlib
open MeasureTheory ProbabilityTheory Set Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_generic_finite_nat_atomic_chain_product
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Z : Fin n → Ω → ℕ)
    (hStep : ∀ (j : Fin n) (v : Fin n → ℕ) (k : ℕ),
      P {ω | (∀ i : Fin n, i < j → Z i ω = v i) ∧ Z j ω = k} =
        P {ω | ∀ i : Fin n, i < j → Z i ω = v i} *
        P {ω | Z j ω = k}) :
    ∀ v : Fin n → ℕ,
      P {ω | ∀ i, Z i ω = v i} =
        ∏ i : Fin n, P {ω | Z i ω = v i} := by sorry
