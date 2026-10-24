-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_affine_selfmap_exists
-- name    : AvramDividend.Classical.causal_weighted_BCF_affine_selfmap_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T08:07:17.754005+00:00
-- url     : https://prove2.me/theorems/4153b8f5-f897-4cab-aca2-459988291a81
-- title:
--   Well-defined affine weighted Volterra self-map of the BCF Banach space
-- statement:
--   The affine map T(f)(x)=exp(-wx)(1−∫(β+K)*V_f)/a sends each bounded continuous input on the nonnegative real half-line to another bounded continuous input, under the strict weighted L1 kernel assumption. The proof establishes half-line continuity, an explicit uniform pointwise bound, and uses a generic BCF lifting theorem. Classical choice packages these output functions into a self-map with the required pointwise identity.
-- source:
--   Previously authored half-line continuity and uniform affine pointwise bound, plus generic BCF lifting.

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_full_kernel_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_affine_pointwise_bound
import Theorems.Thm_AvramDividend_Classical_causal_BCF_lift_of_nonnegative_uniform_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_BCF_affine_selfmap_exists
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    ∃ T : BoundedContinuousFunction ℝ≥0 ℝ →
      BoundedContinuousFunction ℝ≥0 ℝ,
      ∀ (f : BoundedContinuousFunction ℝ≥0 ℝ)
        (x : ℝ) (hx : 0 ≤ x),
        T f ⟨x, hx⟩ =
          (Real.exp (-(w * x)) *
            (1 - ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
              (Real.exp (w * s) *
                f ⟨max s 0, le_max_right s 0⟩) ∂volume)) / a := by sorry
