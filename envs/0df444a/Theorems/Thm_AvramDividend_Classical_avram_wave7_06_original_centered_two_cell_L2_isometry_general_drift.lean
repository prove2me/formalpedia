-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_centered_two_cell_L2_isometry_general_drift
-- name    : AvramDividend.Classical.avram_wave7_06_original_centered_two_cell_L2_isometry_general_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:54:55.715895+00:00
-- url     : https://prove2.me/theorems/ea80f7e1-52d0-4f92-a39a-a4de10ec6bf1
-- title:
--   True original two-cell centred Levy L2 isometry under arbitrary drift
-- statement:
--   Two consecutive actual source increments, each centred by its own original P-expectation, have additive square expectations for the sum, without requiring the uncentred means to vanish. The required square/product integrabilities are explicit and the original independent-increment covariance theorem provides zero cross moment.
-- source:
--   W7-06 arbitrary-drift two-cell original L2 limit precursor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_centered_two_cell_L2_isometry_general_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (hFirst : Integrable (fun ω => X.X (s + u) ω - X.X s ω) P)
    (hSecond : Integrable (fun ω =>
      X.X (s + u + v) ω - X.X (s + u) ω) P)
    (hSqA : Integrable (fun ω =>
      ((X.X (s + u) ω - X.X s ω) -
        (∫ η, X.X (s + u) η - X.X s η ∂P))^2) P)
    (hSqB : Integrable (fun ω =>
      ((X.X (s + u + v) ω - X.X (s + u) ω) -
        (∫ η, X.X (s + u + v) η - X.X (s + u) η ∂P))^2) P)
    (hAB : Integrable (fun ω =>
      ((X.X (s + u) ω - X.X s ω) -
        (∫ η, X.X (s + u) η - X.X s η ∂P)) *
      ((X.X (s + u + v) ω - X.X (s + u) ω) -
        (∫ η, X.X (s + u + v) η - X.X (s + u) η ∂P))) P) :
    (∫ ω,
      (((X.X (s + u) ω - X.X s ω) -
          (∫ η, X.X (s + u) η - X.X s η ∂P)) +
       ((X.X (s + u + v) ω - X.X (s + u) ω) -
          (∫ η, X.X (s + u + v) η - X.X (s + u) η ∂P)))^2 ∂P) =
      (∫ ω, ((X.X (s + u) ω - X.X s ω) -
        (∫ η, X.X (s + u) η - X.X s η ∂P))^2 ∂P) +
      (∫ ω, ((X.X (s + u + v) ω - X.X (s + u) ω) -
        (∫ η, X.X (s + u + v) η - X.X (s + u) η ∂P))^2 ∂P) := by sorry
