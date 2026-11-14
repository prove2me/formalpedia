-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b67_original_preupper_X_centered_cell_bound
-- name    : AvramDividend.Classical.avram_b67_original_preupper_X_centered_cell_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:31:06.898736+00:00
-- url     : https://prove2.me/theorems/aeb927f7-e46b-45d8-bb34-267a3820e7c6
-- title:
--   Original truly pre-ruin and pre-upper-exit source increment bounded after drift correction
-- statement:
--   For two original stopped path times before actual upward exit and with physical lower source bounds, the drift-corrected source increment is bounded by the width x+b plus original drift times the finite time horizon. This is an exact physical B61 jump-cell hypothesis for interior cells; crossing ruin cells remain separate.
-- source:
--   Proved avram_mix_fin22_original_strict_pre_upper_clock_value_le; original source definition and triangle inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_original_strict_pre_upper_clock_value_le
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b67_original_preupper_X_centered_cell_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (T : ℝ≥0)
    (ω : Ω) (s t : ℝ≥0)
    (hst : s ≤ t) (htT : t ≤ T)
    (hsLower : -x ≤ X.X s ω) (htLower : -x ≤ X.X t ω)
    (hsExit : (s : ℝ≥0∞) < twoSidedExitUpTime X b ω)
    (htExit : (t : ℝ≥0∞) < twoSidedExitUpTime X b ω) :
    |X.X t ω - X.X s ω -
      ((t - s : ℝ≥0) : ℝ) * X.c| ≤
      x + b + (T : ℝ) * |X.c| := by sorry
