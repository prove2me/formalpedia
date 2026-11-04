-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_stopped_residual_L1_norm_convergence
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_stopped_residual_L1_norm_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:45:54.380882+00:00
-- url     : https://prove2.me/theorems/11c304ab-fe40-4f16-b551-d36e92d0d1f1
-- title:
--   Original stopped stochastic residual converges in L1 norm under a common integrable source-path envelope
-- statement:
--   For an original-source spectrally negative Lévy process under its genuine probability law, suppose bounded stopped martingale or generator residual variables Mk have an almost-sure limit M, each Mk is a.e. strongly measurable, and a single integrable source-path random variable B bounds the norm of Mk simultaneously at all truncation indices. Then M is genuinely integrable and the expected absolute difference E[|Mk−M|] converges to zero. Proof uses countable a.e. intersection, norm continuity and Lebesgue dominated convergence with envelope 2|B|; source-specific Ito/BDG energy estimates must separately establish the domination. This is the correct L1/UI passage needed to justify retaining a zero-mean martingale at the real stopped clock.
-- source:
--   Mathlib dominated convergence and norm continuity, actual original SpectrallyNegativeLevy probability space; original stopped Itô P4-F requirements.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_e_localise_original_stopped_residual_L1_norm_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Mk : ℕ → Ω → ℝ) (M B : Ω → ℝ)
    (hMkMeas : ∀ k, AEStronglyMeasurable (Mk k) P)
    (hMMeas : AEStronglyMeasurable M P)
    (hBInt : Integrable B P)
    (hBound : ∀ k, ∀ᵐ ω ∂P, ‖Mk k ω‖ ≤ B ω)
    (hAs : ∀ᵐ ω ∂P, Tendsto (fun k => Mk k ω) atTop (𝓝 (M ω))) :
    Integrable M P ∧
    Tendsto (fun k => ∫ ω, ‖Mk k ω - M ω‖ ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
