-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a77_finite_independent_poisson_exp_product
-- name    : AvramDividend.Classical.avram_a77_finite_independent_poisson_exp_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:35:39.038345+00:00
-- url     : https://prove2.me/theorems/200cd6c0-2454-4fef-9b89-ac12ecbeda43
-- title:
--   Finite-family independent Poisson count exponential product identity
-- statement:
--   For any finite family of truly independent same-space Poisson counts, the expectation of the product of exponential count weights equals the product of their exact Poisson generating functions. This is the finite-simple-mark calculation needed for the original Avram a77 physical marked-jump Laplace proof once genuine original-source spatial mark count independence and Poisson marginals are established. It does not assert original jump counts are independent; the required independence is explicit.
-- source:
--   Avram mission physical marked-jump Laplace a77 f4b58008, child 8bbaf3a8. Existing Proved theorem chat06_poisson_count_pgf_general and Mathlib iIndepFun.integral_fun_prod_comp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a77_finite_independent_poisson_exp_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ)
    (N : Fin n → Ω → ℕ)
    (hMeas : ∀ i, Measurable (N i))
    (hIndep : iIndepFun N P)
    (r : Fin n → ℝ≥0)
    (hLaw : ∀ i, HasLaw (N i) (poissonMeasure (r i)) P)
    (a : Fin n → ℝ) :
    (∫ ω, ∏ i, (Real.exp (a i)) ^ N i ω ∂P) =
      ∏ i, Real.exp ((r i : ℝ) * (Real.exp (a i) - 1)) := by sorry
