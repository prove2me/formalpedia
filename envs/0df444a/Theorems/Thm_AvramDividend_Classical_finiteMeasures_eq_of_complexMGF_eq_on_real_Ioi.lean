-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteMeasures_eq_of_complexMGF_eq_on_real_Ioi
-- name    : AvramDividend.Classical.finiteMeasures_eq_of_complexMGF_eq_on_real_Ioi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:35:41.417639+00:00
-- url     : https://prove2.me/theorems/3900afda-9e05-4e96-957b-f3efa07acf50
-- title:
--   Uniqueness of finite probability laws from analytic complex MGFs on an open right half-plane containing the imaginary axis
-- statement:
--   Let μ and ν be finite real Borel measures whose complex moment generating functions are analytic on the same open right half-plane {z : b < Re z}, where b < 0. If those complex MGFs agree at every real argument t > b, then μ = ν. The analytic identity principle on the connected right half-plane extends equality to the imaginary axis, where complex MGFs are characteristic functions. This dualises the already Proved negative-ray uniqueness theorem and enables the positive-exponential-moment Esscher-tilt proof without a forbidden assumption of all-real moments.
-- source:
--   Dual of Proved finiteMeasures_eq_of_complexMGF_eq_on_real_Iio [3c031447-1ce2-436e-933b-fdf2716c0fc1] using pinned Mathlib Convex convex_halfSpace_re_gt, AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq, complexMGF_id_mul_I and Measure.ext_of_charFun; useful for positive-MGF law uniqueness [4fb183cd-2d4f-4df5-8a23-9c6e5b201da0].

import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.NhdsWithin
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

open MeasureTheory Filter Finset Real Complex
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

theorem AvramDividend.Classical.finiteMeasures_eq_of_complexMGF_eq_on_real_Ioi
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (b : ℝ) (hb : b < 0)
    (hμ : AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF id μ)
      {z : ℂ | b < z.re})
    (hν : AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF id ν)
      {z : ℂ | b < z.re})
    (hreal : ∀ t : ℝ, b < t →
      ProbabilityTheory.complexMGF id μ (t : ℂ) =
      ProbabilityTheory.complexMGF id ν (t : ℂ)) :
    μ = ν := by sorry
