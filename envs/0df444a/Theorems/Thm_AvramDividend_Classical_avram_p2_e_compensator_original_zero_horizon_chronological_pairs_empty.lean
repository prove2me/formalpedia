-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_zero_horizon_chronological_pairs_empty
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_zero_horizon_chronological_pairs_empty
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:44:45.588846+00:00
-- url     : https://prove2.me/theorems/4e39f04d-2d2f-45a5-b7a5-37a51e849504
-- title:
--   Original negative-band chronological pair count vanishes at zero physical horizon
-- statement:
--   At physical horizon zero there are no strictly positive original negative-band marked times, so the source-exact chronological pair count is zero.
-- source:
--   Original negative-band jump-time finite set and its literal time window 0<u≤T; zero-horizon boundary case for the second factorial moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_zero_horizon_chronological_pairs_empty
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω 0 n).toFinset
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card = 0 := by sorry
