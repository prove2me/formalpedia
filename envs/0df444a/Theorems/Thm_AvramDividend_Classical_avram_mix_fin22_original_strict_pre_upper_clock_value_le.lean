-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_original_strict_pre_upper_clock_value_le
-- name    : AvramDividend.Classical.avram_mix_fin22_original_strict_pre_upper_clock_value_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:27:10.04047+00:00
-- url     : https://prove2.me/theorems/ddce7de4-a87e-4ed9-8863-5e4469e0c0ff
-- title:
--   Original Lévy path below the true strict upper-exit clock
-- statement:
--   A source-exact stopping-time localisation lemma for the top-cap mixed Itô ledger. If t is strictly earlier than the true upper exit of the original Lévy path at height b, then X_t≤b. Prove by contrapositive of the already Proved strict exceedance implies exit clock at most t. This supplies the pre-exit branch in the compact original path bound needed by c087c2cb and 1bc83b10; the exit-time equality case must additionally use the no-positive-jump result.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_le_observation_of_strict_exceedance
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin22_original_strict_pre_upper_clock_value_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < twoSidedExitUpTime X b ω) :
    X.X t ω ≤ b := by sorry
