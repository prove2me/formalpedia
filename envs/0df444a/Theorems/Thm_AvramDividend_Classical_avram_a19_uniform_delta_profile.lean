-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_delta_profile
-- name    : AvramDividend.Classical.avram_a19_uniform_delta_profile
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:31:33.041594+00:00
-- url     : https://prove2.me/theorems/1b35e77b-7fc4-47e2-9558-4b49d39c0d32
-- title:
--   The uniform physical-grid stopping gap decreases to zero
-- statement:
--   For every positive terminal time T, δ_n = T/(n+2) is positive, at most T, antitone and tends to zero.
-- source:
--   Exact deterministic physical mesh profile needed to instantiate the accepted original stopped cash-prefix integrability and Fatou theorem for the Avram bounded-variation uniform grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_uniform_delta_profile
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    (∀ n, 0 < δ n) ∧ (∀ n, δ n ≤ T) ∧
    Antitone δ ∧ Tendsto δ atTop (nhds (0 : ℝ)) := by sorry
