-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_endpoint_void_ae
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_endpoint_void_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:04:15.234985+00:00
-- url     : https://prove2.me/theorems/74159f8b-770c-46d6-b86b-f447fdf4cdc7
-- title:
--   Original source negative-band void events agree at open and closed horizon endpoint almost surely
-- statement:
--   For the actual Lévy process the no-negative-band-jump event on (0,T) and (0,T] agree almost surely, since a fixed positive time T has no genuine jump on the original source probability space. At T=0 the two events are vacuous. This is the exact endpoint correction needed when converting the target's open interval into an intrinsic Ioc marked count.
-- source:
--   Uses Proved b4407263-9eac-412e-be7a-17c1fecc8ebe. No auxiliary process or jump law assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_endpoint_void_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂P,
      (∀ u : ℝ≥0, 0 < u → u < T →
        ¬ (X.X u ω + 1 / ((n : ℝ) + 1) ≤
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) u)) ↔
      (∀ u : ℝ≥0, u ∈ Ioc 0 T →
        ¬ (X.X u ω + 1 / ((n : ℝ) + 1) ≤
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) u)) := by sorry
