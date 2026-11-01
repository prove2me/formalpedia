-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_reflected_local_time_normalized_at_first_passage
-- name    : AvramDividend.Classical.avram_wave4_02_reflected_local_time_normalized_at_first_passage
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:00:23.00604+00:00
-- url     : https://prove2.me/theorems/badfaab1-84dd-4d07-aea2-2b38ba0b7899
-- title:
--   Actual reflected Lévy local-time clock equals the record level at a finite inverse passage
-- statement:
--   For the actual spectrally negative Lévy sample path, at each finite first strict upward passage u across any nonnegative level b, its normalised running-supremum clock S_u equals b and the reflected drawdown R_u=S_u-X_u equals zero. This is the genuine pathwise inverse-clock normalisation, including the finite endpoint, valid for every sample path and therefore under every genuine finite-clock Esscher tilt. It does not construct an excursion process or a compensator.
-- source:
--   Canonical Proved no-positive-overshoot theorem firstUpcrossing_attains_peak 473109a5 and firstUpcrossing_runningSup_sub_path_eq_zero 9243feef; Kuznetsov-Kyprianou-Rivero (2013), §2.3 choice L_t=S_t.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero

open MeasureTheory Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_reflected_local_time_normalized_at_first_passage
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞))) :
    runningSup X u ω = b ∧ reflectedSup X u ω = 0 := by sorry
