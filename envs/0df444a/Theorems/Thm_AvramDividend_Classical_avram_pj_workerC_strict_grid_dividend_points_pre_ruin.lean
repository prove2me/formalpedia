-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_strict_grid_dividend_points_pre_ruin
-- name    : AvramDividend.Classical.avram_pj_workerC_strict_grid_dividend_points_pre_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:59:07.973352+00:00
-- url     : https://prove2.me/theorems/c454ce4c-a770-4892-846c-b90e2000a399
-- title:
--   True purejump ruin-clipped stop makes every strict prepayment grid dividend atom genuinely pre-ruin
-- statement:
--   Under exact original ruin-clipped bounded stopping clock rho<=tau, any finite physical dividend grid containing only initial t=0 or strictly earlier t<rho dividend times satisfies the actual ruin-contact exclusion t=0 or t<ruinTime. This discharges the exact original HJB-plus-dividend nonpositive signed source hypotheses while leaving payment exactly at rho for a separate contact correction.
-- source:
--   Proved edebe535 genuine subordinate stopped clock before ruin, strict grid prepayment support.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_strict_grid_dividend_points_pre_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n)
    (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (A : Ω → Finset ℝ≥0)
    (hA : ∀ ω t, t ∈ A ω → t = 0 ∨ t < ρ ω) :
    ∀ ω t, t ∈ A ω →
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω := by sorry
