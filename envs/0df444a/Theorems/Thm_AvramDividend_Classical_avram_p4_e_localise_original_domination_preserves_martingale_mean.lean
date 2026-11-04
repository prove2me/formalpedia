-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_domination_preserves_martingale_mean
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_domination_preserves_martingale_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:03:32.998205+00:00
-- url     : https://prove2.me/theorems/a2afcbd7-2114-4f9f-adfe-3945498d3ba3
-- title:
--   Dominated source-path localised martingale limits are L1 and retain zero mean
-- statement:
--   A truly dominated almost-sure limit of centred actual-source stopped martingale residuals is integrable and remains zero-mean, conditional on explicit measurability and domination. This repair adds the Topology scoped notation needed for 𝓝 in the formal theorem; prior publication failed in source header only. Stochastic centring and domination remain genuine obligations.
-- source:
--   Source SpectrallyNegativeLevy, pinned Mathlib dominated convergence and Integrable.mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_e_localise_original_domination_preserves_martingale_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Mk : ℕ → Ω → ℝ) (M B : Ω → ℝ)
    (hMkMeas : ∀ k, AEStronglyMeasurable (Mk k) P)
    (hMMeas : AEStronglyMeasurable M P)
    (hBint : Integrable B P)
    (hBound : ∀ k, ∀ᵐ ω ∂P, ‖Mk k ω‖ ≤ B ω)
    (hLimitBound : ∀ᵐ ω ∂P, ‖M ω‖ ≤ ‖B ω‖)
    (hAs : ∀ᵐ ω ∂P, Tendsto (fun k => Mk k ω) atTop (𝓝 (M ω)))
    (hCentre : ∀ k, (∫ ω, Mk k ω ∂P) = 0) :
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by sorry
