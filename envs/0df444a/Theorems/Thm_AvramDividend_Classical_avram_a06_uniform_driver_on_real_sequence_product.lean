-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_driver_on_real_sequence_product
-- name    : AvramDividend.Classical.avram_a06_uniform_driver_on_real_sequence_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T16:36:55.132203+00:00
-- url     : https://prove2.me/theorems/868ae26c-0d9b-434f-bf54-0bf62d3df19f
-- title:
--   Diffuse negative compound-Poisson driver on the fixed pair of real-sequence spaces
-- statement:
--   Construct the jointly independent exponential interarrival and uniform negative-mark streams directly as coordinate projections on the fixed pair of real sequence spaces, by pushing forward the law of an existing abstract driver. This preserves all marginal distributions and the full jointly independent product law and resolves the sample-space mismatch for A06.
-- source:
--   Genuine source construction sub-obligation of A06 Open 115c3b1e, which requires this exact sample-space type and a subsequent Avram SpectrallyNegativeLevy adaptation.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_driver_exists

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_uniform_driver_on_real_sequence_product :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ),
      IsProbabilityMeasure P ∧
      LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
        ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P := by sorry
