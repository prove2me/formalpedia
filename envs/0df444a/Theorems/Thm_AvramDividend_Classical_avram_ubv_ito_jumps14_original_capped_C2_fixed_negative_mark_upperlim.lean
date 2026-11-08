-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:41:40.424618+00:00
-- url     : https://prove2.me/theorems/5864c4ee-68cd-49ef-a49c-69097e3b20fc
-- title:
--   Original capped C2 Lévy value yields fixed-negative-mark Taylor upper mesh limit across ruin contact
-- statement:
--   For the original candidate value satisfying the UBV cap-local C2 condition, a positive compact interior reserve and a fixed negative Lévy mark, the original Taylor jump correction has a one-sided upper mesh limit even when the post-jump reserve lands exactly at zero. The proof derives continuity of the value and its derivative from the original cap-local C2 assumptions and applies the previously Proved fixed-mark upper limit. This bridges the exact-zero-contact case omitted by the earlier full-continuity statement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
    (w : ℝ → ℝ) (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (y z : ℝ) (hy : y ∈ Ioo (0 : ℝ) c) (hz : z < 0)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds y)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      w (u n + z) - w (u n) -
        (if -1 < z then z * deriv w (u n) else 0) ≤
      w (y + z) - w y -
        (if -1 < z then z * deriv w y else 0) + ε := by sorry
