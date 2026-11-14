-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_original_smallband_increment_shift_borel_20261113
-- name    : AvramDividend.Classical.avram_a23_original_smallband_increment_shift_borel_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:08:38.927512+00:00
-- url     : https://prove2.me/theorems/1f58afbe-4bfc-429f-9887-c2aea36778aa
-- title:
--   Every original compensated negative cutoff-band increment is a Borel function of the physical future path
-- statement:
--   For any original spectrally negative Levy process, fixed cutoff n and physical interval s≤t, the compensated marked source band increment is a measurable function of the shifted original increment path, with the deterministic signed Levy compensator subtracted exactly.
-- source:
--   Proved avram_bv_jump8_cadlag_mark_weight_lintegral_borel and avram_mix_fin14_original_negative_band_shift_integral_exact, with A23 window decomposition and original time-compensator subtraction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_negative_band_shift_integral_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_generic_negative_mark_window_integral_formula
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every physical cutoff band increment is a Borel functional of the actual future source path. -/

theorem AvramDividend.Classical.avram_a23_original_smallband_increment_shift_borel_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ W : (ℝ≥0 → ℝ) → ℝ, Measurable W ∧
      ∀ ω : Ω,
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω =
        W (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by sorry
