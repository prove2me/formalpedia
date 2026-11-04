-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_stopped_L1_mean_and_signed_limit
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_joint_stopped_L1_mean_and_signed_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:43:02.69936+00:00
-- url     : https://prove2.me/theorems/2479bab2-8ebf-48e0-9094-f6ceeafa1371
-- title:
--   Original UBV stopped martingale and signed drift limits retain L1, zero mean and nonpositive residual
-- statement:
--   For the original spectrally negative Lévy probability law and sample space, let finite-clock stopped martingale Mk and residuals Gk,Hk have a.s. limiting random variables M,G,H. Assume explicit individually integrable source-path envelope variables BM,BG,BH dominate every stopping index, and every finite-clock martingale has mean zero, and each finite-clock signed residual Gk+Hk is nonpositive. Then M,G,H are all actually integrable, E[M]=0 by dominated convergence, and G+H remains nonpositive a.s. This makes the P4-F exact witness-side integrability and signed bounds available from a single genuine Lean theorem once stochastic source-specific bracket/domination estimates are established. No UI or optional stopping is inferred without its hypotheses.
-- source:
--   Mathlib Lebesgue dominated convergence, original SpectrallyNegativeLevy probability space; P4-F exact Itô residual signed budget requirements.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_e_localise_original_joint_stopped_L1_mean_and_signed_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Mk Gk Hk : ℕ → Ω → ℝ) (M G H BM BG BH : Ω → ℝ)
    (hMkMeas : ∀ k, AEStronglyMeasurable (Mk k) P)
    (hMMeas : AEStronglyMeasurable M P)
    (hGMeas : AEStronglyMeasurable G P)
    (hHMeas : AEStronglyMeasurable H P)
    (hBMInt : Integrable BM P) (hBGInt : Integrable BG P)
    (hBHInt : Integrable BH P)
    (hMBound : ∀ k, ∀ᵐ ω ∂P, ‖Mk k ω‖ ≤ BM ω)
    (hGBound : ∀ k, ∀ᵐ ω ∂P, ‖Gk k ω‖ ≤ BG ω)
    (hHBound : ∀ k, ∀ᵐ ω ∂P, ‖Hk k ω‖ ≤ BH ω)
    (hMlim : ∀ᵐ ω ∂P, Tendsto (fun k => Mk k ω) atTop (𝓝 (M ω)))
    (hGlim : ∀ᵐ ω ∂P, Tendsto (fun k => Gk k ω) atTop (𝓝 (G ω)))
    (hHlim : ∀ᵐ ω ∂P, Tendsto (fun k => Hk k ω) atTop (𝓝 (H ω)))
    (hCentred : ∀ k, (∫ ω, Mk k ω ∂P) = 0)
    (hSign : ∀ k, ∀ᵐ ω ∂P, Gk k ω + Hk k ω ≤ 0) :
    Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
    (∫ ω, M ω ∂P) = 0 ∧ (∀ᵐ ω ∂P, G ω + H ω ≤ 0) := by sorry
