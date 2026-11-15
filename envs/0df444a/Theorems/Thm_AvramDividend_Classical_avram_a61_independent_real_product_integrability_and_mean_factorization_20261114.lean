-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a61_independent_real_product_integrability_and_mean_factorization_20261114
-- name    : AvramDividend.Classical.avram_a61_independent_real_product_integrability_and_mean_factorization_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:27:07.264923+00:00
-- url     : https://prove2.me/theorems/ab0be9fd-2dbe-4ca0-a3b9-c11e3d2b4466
-- title:
--   Independent nonzero real source factor and integrable product imply integrability of the other factor and exact product-expectation factorisation
-- statement:
--   For independent measurable real random variables on the same original probability space, if their product is integrable and the second factor is nonzero with positive probability, then the first factor is integrable and the product expectation factors exactly.
-- source:
--   Pinned Mathlib IndepFun.integrable_left_of_integrable_op and IndepFun.integral_mul_eq_mul_integral.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Independent nonzero real factors: integrability of the product implies integrability of the left factor and exact mean factorisation. -/

theorem AvramDividend.Classical.avram_a61_independent_real_product_integrability_and_mean_factorization_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F J : Ω → ℝ)
    (hMF : Measurable F) (hMJ : Measurable J)
    (hInd : F ⟂ᵢ[P] J)
    (hProd : Integrable (fun ω => F ω * J ω) P)
    (hNonzero : ¬ (J =ᵐ[P] fun _ => (0 : ℝ))) :
    Integrable F P ∧
      (∫ ω, F ω * J ω ∂P) =
        (∫ ω, F ω ∂P) * (∫ ω, J ω ∂P) := by sorry
