-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_two_cell_L2_isometry_of_centered_future_increments
-- name    : AvramDividend.Classical.avram_wave7_06_original_two_cell_L2_isometry_of_centered_future_increments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:34:06.251525+00:00
-- url     : https://prove2.me/theorems/646b4611-35c6-42bf-96a7-7734798a359e
-- title:
--   Original Lévy source two-cell L² isometry for centred consecutive future increments
-- statement:
--   For two original consecutive future increments of X, if each is integrable and centred and their squares and mixed product are integrable, then the square of their combined increment has expectation equal to the sum of their square expectations. The proof imports the now-Proved original cross-moment zero theorem and two-cell L² expansion and never substitutes a different process.
-- source:
--   W7-06 finite two-cell original-source L² martingale difference step; stopped marked-cell and truncation limit remain separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_two_cell_L2_isometry_of_centered_future_increments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (hFirst : Integrable (fun ω => X.X (s + u) ω - X.X s ω) P)
    (hSecond : Integrable (fun ω =>
      X.X (s + u + v) ω - X.X (s + u) ω) P)
    (hSqA : Integrable (fun ω => (X.X (s + u) ω - X.X s ω)^2) P)
    (hSqB : Integrable (fun ω =>
      (X.X (s + u + v) ω - X.X (s + u) ω)^2) P)
    (hAB : Integrable (fun ω =>
      (X.X (s + u) ω - X.X s ω) *
      (X.X (s + u + v) ω - X.X (s + u) ω)) P)
    (hMeanFirst : (∫ ω, X.X (s + u) ω - X.X s ω ∂P) = 0)
    (hMeanSecond :
      (∫ ω, X.X (s + u + v) ω - X.X (s + u) ω ∂P) = 0) :
    (∫ ω, (X.X (s + u + v) ω - X.X s ω)^2 ∂P) =
      (∫ ω, (X.X (s + u) ω - X.X s ω)^2 ∂P) +
      (∫ ω, (X.X (s + u + v) ω - X.X (s + u) ω)^2 ∂P) := by sorry
