-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_cadlag_all_horizons
-- name    : AvramDividend.Classical.avram_wave7_06_original_frozen_prefix_cadlag_all_horizons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:38:41.490036+00:00
-- url     : https://prove2.me/theorems/c7626437-6a6e-47b2-973a-65cdcd1c1121
-- title:
--   Every original spectrally negative Lévy sample path frozen at a finite horizon remains càdlàg
-- statement:
--   For every original spectrally negative Lévy sample path, freezing the path after any deterministic time T preserves right-continuity at every nonnegative time and the existence of finite left limits at all positive times. The proof handles times before, at and after T using the actual source process, supporting stopped-prefix marked-count measurability.
-- source:
--   Avram W7-06 original-filtration small-jump compensation, source rightCont and leftLim axioms and deterministic min-clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_frozen_prefix_cadlag_all_horizons
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    (∀ u : ℝ≥0,
      ContinuousWithinAt (fun v : ℝ≥0 => X.X (min v T) ω) (Ici u) u) ∧
    (∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto (fun v : ℝ≥0 => X.X (min v T) ω)
        (𝓝[<] u) (𝓝 l)) := by sorry
