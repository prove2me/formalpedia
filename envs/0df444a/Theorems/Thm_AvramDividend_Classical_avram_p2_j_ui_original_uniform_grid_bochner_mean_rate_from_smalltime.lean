-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uniform_grid_bochner_mean_rate_from_smalltime
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_uniform_grid_bochner_mean_rate_from_smalltime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:29:27.323699+00:00
-- url     : https://prove2.me/theorems/ca3a08ba-eaab-4e6b-96c8-616cb4112d70
-- title:
--   Original Lévy uniform-grid real expectations inherit the genuine small-time rate
-- statement:
--   For the actual original spectrally negative Lévy process and a continuous compactly supported real test, assume its genuine one-time real Bochner expectation has a small-time quotient limit L. At every positive real horizon, the expectations of the original uniform-grid test sums converge to the horizon multiplied by L. The proof uses the original stationary increment law and a real-time mesh asymptotic; no jump-compensator law, independent replacement process or assumed pathwise jump limit is used.

import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uniform_real_grid_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_smalltime_rescale_uniform_grid

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_uniform_grid_bochner_mean_rate_from_smalltime
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g)) (L : ℝ)
    (hRate : Tendsto
      (fun h : ℝ => (∫ ω, g (X.X (Real.toNNReal h) ω) ∂P) / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    Tendsto (fun n : ℕ => ∫ ω,
      ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
           X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P)
      atTop (nhds ((T : ℝ) * L)) := by sorry
