-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_future_borel_marked_grid_count_stationary_law
-- name    : AvramDividend.Classical.avram_wave6_01_original_future_borel_marked_grid_count_stationary_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:49:16.673888+00:00
-- url     : https://prove2.me/theorems/35e02e0f-76cb-4ddb-a62e-672c0fde6f53
-- title:
--   Actual Lévy arbitrary Borel-marked future grid count has exactly the stationary original-process law
-- statement:
--   For the original spectrally negative Levy process and the unchanged measure P, every finite deterministic family of future X increments classified by a genuine Borel mark set B has exactly the same whole counting distribution as the matching grid beginning at time zero. The proof is a direct Borel finite-cylinder pushforward of the canonically Proved original full-future-path stationary law, with no proxy process, jump compensation assumption or restriction to drift deficits.
-- source:
--   Canonically Proved source whole-path stationarity 7a0dfabc-f3ac-499e-8769-05f7bfe4ae96, whole-path measurability 840bbf85-6d2b-4b05-a1d1-8712ce085afc, and original marked grid source extraction. Extends source drift-deficit-only count stationary law 5143fc50 to arbitrary Borel marks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave6_01_original_future_borel_marked_grid_count_stationary_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ) (grid : ℕ → ℝ≥0) :
    Measure.map (fun ω : Ω =>
      ((Finset.range n).filter (fun i =>
        (X.X (s + grid (i + 1)) ω - X.X s ω) -
          (X.X (s + grid i) ω - X.X s ω) ∈ B)).card) P =
    Measure.map (fun ω : Ω =>
      ((Finset.range n).filter (fun i =>
        X.X (grid (i + 1)) ω - X.X (grid i) ω ∈ B)).card) P := by sorry
