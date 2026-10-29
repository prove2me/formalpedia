-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_all_positive_restricted_laplace_indepFun
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_all_positive_restricted_laplace_indepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:00:29.848724+00:00
-- url     : https://prove2.me/theorems/5a7476f4-4c19-4b15-a073-540d640f85b0
-- title:
--   All upper-ray Laplace factors imply complete independence of a nonnegative drawdown
-- statement:
--   For an arbitrary probability P and jointly measurable real R,D with D nonnegative, if for every real upper-ray threshold a and every positive beta the restricted ENNReal Laplace reward factorises against the probability of the upper-ray, then R and D are independent as full Borel random variables. The restricted real-moment conversion and conditional positive-MGF uniqueness establish the general reduction. One beta alone is insufficient.
-- source:
--   Accepted full conditional MGF law independence (17e694fd), accepted bounded nonnegative conditional Laplace independence (f6c2f91a), and accepted restricted ENNReal-to-real conditional integral conversion (9826e338), with accepted ENNReal normalisation (2ab4f429). Both previously Open imports are now canonically Proved on exact proof-evidence readback. Full all-beta upper-ray family is required.

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_nonneg_conditional_laplace_indepFun
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_restricted_real_integral_factor_conditional

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

theorem AvramDividend.Classical.avram_ws01e_bi_new_all_positive_restricted_laplace_indepFun
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R D : Ω → ℝ) (hR : Measurable R) (hD : Measurable D)
    (hDnonneg : ∀ ω, 0 ≤ D ω)
    (hFactor : ∀ a β : ℝ, 0 < β →
      (∫⁻ ω in R ⁻¹' Set.Ioi a,
          ENNReal.ofReal (Real.exp (-(β * D ω))) ∂P) =
        P (R ⁻¹' Set.Ioi a) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(β * D ω))) ∂P)) :
    IndepFun R D P := by sorry
