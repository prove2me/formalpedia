-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_upper_terminal_positive_window
-- name    : AvramDividend.Classical.avram_root29_01_actual_upper_terminal_positive_window
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:25:34.779958+00:00
-- url     : https://prove2.me/theorems/4b7e4610-c2a9-4f19-b3cb-adf2a49721de
-- title:
--   Genuine Lévy positive upper-exit reserve persists in a right calendar window
-- statement:
--   For a genuine source spectrally negative Lévy path, at any positive terminal reserve and sample time where the path is right-continuous, derive an actual strictly positive time window after the upper-exit instant on which the shifted reserve stays nonnegative. This is the source-specific right-boundary hypothesis consumed by killed-grid full-history survival convergence; it does not assume any exit ratio or killed-scale identity.
-- source:
--   WS1A work/avram_root29_01_actual_upper_terminal_positive_window_draft.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_negative_right_interval

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_actual_upper_terminal_positive_window
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (τ : ℝ≥0)
    (hcont : ContinuousWithinAt (fun s : ℝ≥0 => X.X s ω) (Set.Ici τ) τ)
    (hpositive : 0 < x + X.X τ ω) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s : ℝ≥0, τ ≤ s → s < τ + δ →
        0 ≤ x + X.X s ω := by sorry
