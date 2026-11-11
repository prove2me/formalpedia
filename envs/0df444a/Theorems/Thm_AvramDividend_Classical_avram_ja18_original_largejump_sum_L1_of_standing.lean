-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_largejump_sum_L1_of_standing
-- name    : AvramDividend.Classical.avram_ja18_original_largejump_sum_L1_of_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T20:25:15.639414+00:00
-- url     : https://prove2.me/theorems/37d22393-44f1-4873-ab42-38090e68bcc5
-- title:
--   Original large-negative-jump physical sum is L1 under Standing
-- statement:
--   For the original spectrally negative Levy process with Standing and finite negative jump activity, the original uncompensated sum of actual negative jumps of size at least one is integrable at every fixed time. Standing is indispensable: finite jump intensity by itself does not imply finite expected absolute jump size.
-- source:
--   Sound remaining finite-activity integrability prerequisite for 70393ec7 after the Proved original X_t L1 theorem ecbf4e66. Existing Proved exact source finite support e8675ada, original small-band L1 c321c303. Prove from the actual original process first moment and its jump-measure decomposition; no invented independent auxiliary PRM or gratuitous large-jump first-moment axiom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_largejump_sum_L1_of_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) P := by sorry
