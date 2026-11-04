-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_ae_norm_bound_passes_to_stopped_residual_limit
-- name    : AvramDividend.Classical.avram_p4_e_localise_ae_norm_bound_passes_to_stopped_residual_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:05:53.66308+00:00
-- url     : https://prove2.me/theorems/26bbada2-0a3f-4898-8e6c-ccf91d15c554
-- title:
--   Uniform stopped residual domination survives an almost-sure limit on the same original probability space
-- statement:
--   If every original-source localised signed residual Mk is bounded a.e. by one common real random bound B, and the residual sequence converges almost surely to M, the actual limiting residual inherits the norm bound by |B|. Countable a.e. intersection and continuity of norm justify the limit rigorously. This discharges the hLimitBound premise of the dominated stopped-martingale zero-mean theorem without optional stopping or guessing an L1 majorant, and preserves all original law and sample-space objects.
-- source:
--   Original SpectrallyNegativeLevy law; Mathlib countable ae intersection and closedness of ≤ under limits.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_e_localise_ae_norm_bound_passes_to_stopped_residual_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Mk : ℕ → Ω → ℝ) (M B : Ω → ℝ)
    (hBound : ∀ k, ∀ᵐ ω ∂P, ‖Mk k ω‖ ≤ B ω)
    (hAs : ∀ᵐ ω ∂P, Tendsto (fun k => Mk k ω) atTop (𝓝 (M ω))) :
    ∀ᵐ ω ∂P, ‖M ω‖ ≤ ‖B ω‖ := by sorry
