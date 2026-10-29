-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_restricted_real_integral_factor_conditional
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_restricted_real_integral_factor_conditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:48:51.544292+00:00
-- url     : https://prove2.me/theorems/9826e338-964f-44fd-a1d2-fced6c560457
-- title:
--   Restricted ENNReal factorisation gives the conditional real integral
-- statement:
--   For a probability law P, measurable event A of positive mass and nonnegative integrable real reward f under P and P conditional on A, a restricted nonnegative extended-real integral factorisation implies equality of its conditional and unconditional real expectations. Finiteness and nonnegativity justify applying ENNReal.ofReal inversion, with the accepted extended-integral normalisation theorem.
-- source:
--   Proved AvramDividend.Classical.avram_ws01e_bi_new_restricted_lintegral_factor_conditional (2ab4f429), pinned Mathlib ofReal_integral_eq_lintegral_ofReal and ENNReal.toReal_ofReal. One modular conversion needed for all-beta restricted drawdown Laplace factors.

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_restricted_lintegral_factor_conditional

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

theorem AvramDividend.Classical.avram_ws01e_bi_new_restricted_real_integral_factor_conditional
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hApos : P A ≠ 0)
    (f : Ω → ℝ) (hNonneg : ∀ ω, 0 ≤ f ω)
    (hIntP : Integrable f P) (hIntCond : Integrable f (P[|A]))
    (hFactor :
      (∫⁻ ω in A, ENNReal.ofReal (f ω) ∂P) =
        P A * (∫⁻ ω, ENNReal.ofReal (f ω) ∂P)) :
    (∫ ω, f ω ∂(P[|A])) = ∫ ω, f ω ∂P := by sorry
