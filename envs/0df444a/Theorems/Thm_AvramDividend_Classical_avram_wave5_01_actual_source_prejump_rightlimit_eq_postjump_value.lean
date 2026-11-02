-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_prejump_rightlimit_eq_postjump_value
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_prejump_rightlimit_eq_postjump_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:41:50.32401+00:00
-- url     : https://prove2.me/theorems/ae89b008-ddc2-477a-aa13-455960e9fe39
-- title:
--   Right-hand limit of actual original Lévy pre-jump path equals original post-jump source value
-- statement:
--   For every sample of the original SpectrallyNegativeLevy P 𝓕 and every nonnegative time t, the strict-right limit of the same-path pre-jump left-limit process is exactly the genuine right-continuous Lévy value X_t. This is the source-specific càglàd recovery identity, with no BV, Poisson-copy, filtered extension or exceptional sample event. It supports deterministic right-neighbourhood control needed for genuine finite-band jump localisation and chronological source/dividend accounting.
-- source:
--   Original X.rightCont; pinned Mathlib ContinuousWithinAt.rightLim_eq, rightLim_leftLim and nhdsWithin_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_prejump_rightlimit_eq_postjump_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) :
    Function.rightLim
      (fun u : ℝ≥0 => Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
      t = X.X t ω := by sorry
