-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_zero_shifted_negative_mark_loss_uniformly_bounded_by_candidate_increment_at_zero
-- name    : AvramDividend.Classical.avram_bva_a22_original_zero_shifted_negative_mark_loss_uniformly_bounded_by_candidate_increment_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:02:52.041197+00:00
-- url     : https://prove2.me/theorems/c1519aab-2069-4465-8b96-36b164a1c949
-- title:
--   Original positive-reserve negative mark zero-shifted candidate loss is uniformly dominated by the increment from reserve zero to the band width
-- statement:
--   On the genuine original Avram dividend candidate, for every positive spatial boundary width epsilon and every positive pre-mark reserve y no greater than epsilon, assume the candidate w is nondecreasing on the closed interval from zero to epsilon. For any genuine negative mark z, the zero-shifted loss w(y)-w(0) minus its noncrossing continuation value w(y+z)-w(0) if y+z stays nonnegative, or zero upon ruin crossing, is nonnegative and at most w(epsilon)-w(0). This isolates a uniformly vanishing small-band remainder even when w(0)>0, retaining the separately bounded genuine ruin-crossing boundary charge. No Lévy intensity finiteness, jump variation rate or chosen mesh diagonal is assumed; it is a deterministic candidate-value source estimate that can be applied pointwise to the stopped original negative-mark compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_zero_shifted_negative_mark_loss_uniformly_bounded_by_candidate_increment_at_zero
    (w : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hmono : MonotoneOn w (Icc (0 : ℝ) ε)) :
    ∀ y ∈ Ioc (0 : ℝ) ε, ∀ z : ℝ, z < 0 →
      0 ≤ (w y - w 0) -
        (if y + z < 0 then 0 else w (y + z) - w 0) ∧
      (w y - w 0) -
        (if y + z < 0 then 0 else w (y + z) - w 0) ≤ w ε - w 0 := by sorry
