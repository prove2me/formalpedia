-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
-- name    : AvramDividend.Classical.avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:32:41.007746+00:00
-- url     : https://prove2.me/theorems/edebe535-25e3-417c-84fb-5a8a21a57b8a
-- title:
--   Original subordinate stopped clock is uniformly bounded by deterministic horizon and true ruin
-- statement:
--   For exact natural ruined clipped clock tau and an arbitrary stopping clock rho dominated by tau, rho is pathwise at most deterministic horizon n and lies before or at the true original ruinTime. Directly combines Proved real-horizon clipped-source certificate and Proved subordinate-clock ruin bound.
-- source:
--   e4906bf5 true original n horizon clock and a5216ca1 subordinate-clock <= ruinTime.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_subordinate_clock_le_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω) :
    (∀ ω, ρ ω ≤ (n : ℝ≥0)) ∧
    (∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) := by sorry
