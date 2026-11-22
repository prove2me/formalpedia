-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_fixed_finite_negative_marks_capped_Taylor_signed_positive_zero
-- name    : AvramDividend.Classical.avram_freshD_original_fixed_finite_negative_marks_capped_Taylor_signed_positive_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:47:22.719603+00:00
-- url     : https://prove2.me/theorems/2bbf2425-f9ec-4c96-978c-adc45570a092
-- title:
--   True original cap-local C2 Taylor upper-bound survives finite negative mark sums even at exact ruin zero
-- statement:
--   For the original Avram cap-local C2 candidate w with zero extension to negative reserve, a fixed interior pre-jump state y and any finite set of genuine negative mark values z, when approximating sampled prestate u(m) tends to y, the positive part of the sum of all nonlinear source Taylor mark approximation errors converges to zero. The same fixed-mark upper inequality already Proved as avram_ubv_ito_jumps14 handles marks exactly landing at reserve zero without the false assumption w(0)=0. Apply the single-mark eventual upper bound with a/(card S + 1) and finite intersection, sum and use the order characterisation of convergence to zero. A future source-faithful coupling to actual marked physical stopped cells still must be proved.
-- source:
--   Original AvramDividend finite-activity mixed Gaussian jump Itô–Stieltjes theorem 242ca5f1; extracts finite-mark uniform eventual upper-sum consequence of the proved original one-sided fixed-negative-mark zero-contact Taylor limit 5864c4ee.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_fixed_finite_negative_marks_capped_Taylor_signed_positive_zero
    (w : ℝ → ℝ) (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) c)
    (S : Finset ℝ) (hS : ∀ z ∈ S, z < 0)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 y)) :
    Tendsto
      (fun m => max
        (∑ z ∈ S,
          ((w (u m + z) - w (u m) -
            (if -1 < z then z * deriv w (u m) else 0)) -
          (w (y + z) - w y -
            (if -1 < z then z * deriv w y else 0)))) 0)
      atTop (𝓝 (0 : ℝ)) := by sorry
