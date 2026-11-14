-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_original_future_path_borel_functional_stationary_law_20261113
-- name    : AvramDividend.Classical.avram_a23_original_future_path_borel_functional_stationary_law_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:21:19.322703+00:00
-- url     : https://prove2.me/theorems/97a0ac57-9a23-4425-b337-b1b795911734
-- title:
--   Every measurable statistic of the original shifted future-increment path has its initial law
-- statement:
--   For the actual spectrally negative Levy source on the original probability space, composing any Borel real functional with the deterministic-time shifted source increment path has the same law as composing it with the initial source path.
-- source:
--   Proved f7f7d00c source shifted-future-path stationarity and Mathlib Measure.map_map.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every Borel functional of the original Levy shifted future path has the initial-path law. -/

theorem AvramDividend.Classical.avram_a23_original_future_path_borel_functional_stationary_law_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (W : (ℝ≥0 → ℝ) → ℝ) (hW : Measurable W) :
    Measure.map (fun ω : Ω => W (fun u : ℝ≥0 =>
      X.X (s + u) ω - X.X s ω)) P =
    Measure.map (fun ω : Ω => W (fun u : ℝ≥0 =>
      X.X u ω)) P := by sorry
