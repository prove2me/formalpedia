-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_preterminal_uniform_grid_precontact_times
-- name    : AvramDividend.Classical.avram_pj_workerC_original_preterminal_uniform_grid_precontact_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:31:02.90728+00:00
-- url     : https://prove2.me/theorems/80e8ad83-8f26-4a82-8fde-4e5c6a3fbb64
-- title:
--   Every preterminal point of the genuine uniform finite grid is zero or strictly before true ruin even at the clipped ruin contact
-- statement:
--   For any original stopped clock rho bounded above by the true ruinTime, define the exact physical uniform preterminal grid times rho*i/k for i=0,...,k-1. Every grid time is either the initial zero atom or strictly before true ruin, including rho=ruin, because i/k<1 when k>0 and rho>0. The terminal contact time itself is deliberately excluded. This is the precise hPre assumption required for the Proved finite-grid HJB/right-payment nonpositive Q theorem and preserves the ruin overshoot convention.
-- source:
--   Original stopped-clock ruin domination hρruin; exact Finset.range k rational physical mesh preterminal geometry. No additional stochastic hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_preterminal_uniform_grid_precontact_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ρ : Ω → ℝ≥0)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (k : ℕ) (hk : 0 < k) :
    let A : Ω → Finset ℝ≥0 := fun ω =>
      (Finset.range k).image
        (fun i : ℕ => ρ ω * ((i : ℝ≥0) / (k : ℝ≥0)))
    ∀ ω t, t ∈ A ω →
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω := by sorry
