-- Prove2me | solution 1 for re_inner_smul_resolvent_circleMap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:32.493355+00:00
-- url     : https://prove2.me/submissions/141349da-0767-4d0c-971f-db4f8f74c426

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Theorems.Thm_re_inner_smul_resolvent_nonneg

set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hW : numericalRange A ⊆ Metric.closedBall c R) (t : ℝ) (x : E) :
    0 ≤ (⟪x, ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)) x⟫_ℂ).re := by
  refine re_inner_smul_resolvent_nonneg A (fun w hw => ?_) x
  have hwc : dist w c ≤ R := Metric.mem_closedBall.mp (hW hw)
  have hR : 0 ≤ R := le_trans dist_nonneg hwc
  have hζ : ‖circleMap 0 R t‖ = R := by rw [norm_circleMap_zero, abs_of_nonneg hR]
  have hν : -I * deriv (circleMap c R) t = circleMap 0 R t := by
    rw [deriv_circleMap]
    linear_combination (-circleMap 0 R t) * I_sq
  have hsub : w - circleMap c R t = (w - c) - circleMap 0 R t := by
    rw [← circleMap_sub_center c R t]
    ring
  have h1 : ((starRingEnd ℂ) (circleMap 0 R t) * (w - c)).re ≤ R * dist w c := by
    calc ((starRingEnd ℂ) (circleMap 0 R t) * (w - c)).re
        ≤ ‖(starRingEnd ℂ) (circleMap 0 R t) * (w - c)‖ := Complex.re_le_norm _
      _ = R * dist w c := by rw [norm_mul, Complex.norm_conj, hζ, dist_eq_norm]
  have h2 : ((starRingEnd ℂ) (circleMap 0 R t) * circleMap 0 R t).re = R ^ 2 := by
    rw [Complex.conj_mul', hζ, ← Complex.ofReal_pow, Complex.ofReal_re]
  have h3 : R * dist w c ≤ R * R := mul_le_mul_of_nonneg_left hwc hR
  rw [hν, hsub, mul_sub, Complex.sub_re]
  linarith [h1, h2, h3]
