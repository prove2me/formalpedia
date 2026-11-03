-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_right_continuous
-- name    : AvramDividend.Classical.avram_wave7_06_original_frozen_prefix_right_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T22:32:11.658911+00:00
-- url     : https://prove2.me/theorems/09fd3ede-b34e-47ad-a52f-6e1c7aa77fcb
-- title:
--   Genuine original Lévy path remains right-continuous after deterministic freezing
-- statement:
--   For any original spectrally negative Lévy sample path and any deterministic stopping horizon T, the time-frozen path v↦X(min(v,T),ω) is right-continuous at every nonnegative time. This is a direct consequence of source right-continuity and monotone continuous clock composition, supporting raw-filtration marked-count measurability.
-- source:
--   W7-06 actual original-process stopped marked-jump filtration bridge, source rightCont axiom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_frozen_prefix_right_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    ∀ u : ℝ≥0,
      ContinuousWithinAt
        (fun v : ℝ≥0 => X.X (min v T) ω) (Ici u) u := by sorry
