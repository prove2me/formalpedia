-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_zero_start_stopped_scale_of_down_exit_zero
-- name    : AvramDividend.Classical.chat04_unbounded_zero_start_stopped_scale_of_down_exit_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:44:34.101447+00:00
-- url     : https://prove2.me/theorems/8029c619-18d2-4bb2-af3b-90196ce32411
-- title:
--   Two-sided stopped q-scale identity at zero capital from instantaneous downward exit
-- statement:
--   For the unbounded-variation q-scale function W, W(0)=0. If the strict downward passage time below initial reserve zero is almost surely zero, the event that the upward strict passage time occurs before downward passage is impossible. Its discounted ENNReal integral is zero and the two-sided stopped-scale balance holds for starting capital zero. The theorem isolates the exact path-regularity hypothesis needed at the boundary of the parent stopped-scale identity.
-- source:
--   Direct x=0 boundary of the Open AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity (aed50a34-200b-4736-a369-5ae8473e3258), itself root-connected via the accepted two-sided exit reductions. Imports Proved chat04_scale_zero_origin_of_unbounded_variation (c1b8958a-41fd-444e-893e-cf03e591b93e). Independent of the positive-state killed q-scale martingale.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_zero_start_stopped_scale_of_down_exit_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hdown0 : ∀ᵐ ω ∂P,
      (⨅ (t : ℝ≥0) (_ : X.X t ω < 0), (t : ℝ≥0∞)) = 0) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < 0), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W 0) := by sorry
