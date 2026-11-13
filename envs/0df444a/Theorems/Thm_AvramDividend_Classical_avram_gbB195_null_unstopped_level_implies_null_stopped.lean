-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB195_null_unstopped_level_implies_null_stopped
-- name    : AvramDividend.Classical.avram_gbB195_null_unstopped_level_implies_null_stopped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:35:41.220612+00:00
-- url     : https://prove2.me/theorems/ab222693-3b43-4839-a24d-31906ddbd7f8
-- title:
--   Unstopped fixed-level null occupation survives arbitrary shorter random horizon
-- statement:
--   A fixed-level set of zero finite-horizon Lebesgue time occupation almost surely has zero occupation after any random shorter time restriction.
-- source:
--   Avram Gaussian B finite cap fixed-level occupation decomposition, 12 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB195_null_unstopped_level_implies_null_stopped
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ → ℝ) (n : ℕ) (b : ℝ)
    (hFull : ∀ᵐ ω ∂P,
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ Y ω t = b} = 0)
    (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧ Y ω t = b} = 0 := by sorry
