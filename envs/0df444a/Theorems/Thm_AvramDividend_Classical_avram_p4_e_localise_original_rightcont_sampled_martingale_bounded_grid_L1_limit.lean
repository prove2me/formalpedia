-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_rightcont_sampled_martingale_bounded_grid_L1_limit
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_rightcont_sampled_martingale_bounded_grid_L1_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:51:31.665218+00:00
-- url     : https://prove2.me/theorems/ca9457ed-c022-4e33-9768-5ee4af95f505
-- title:
--   Original right-continuous filtration sampled true martingale stopped L1 limit is centred
-- statement:
--   The canonical ruin-truncated UBV clock is proved a stopping time in the original right-continuous filtration. This source-exact helper samples a genuine Martingale f 𝓕.rightCont P on a monotone original-time grid and optional-stops it in the sampled 𝓕.rightCont filtration, then uses explicit common L1 domination and almost-sure convergence to conclude the limit is Integrable and centred. The original source X and raw filtration 𝓕 are unchanged. Unlike the earlier raw-𝓕 sampled version, this hypothesis matches the canonical rightCont stopping-time interface; proving the actual source stochastic integrand is a rightCont martingale remains separate.
-- source:
--   Uses the already-Proved monotone-sampling bounded optional stopping theorem and original P4-E dominated L1 martingale mean limit; conservatively retains the raw source X : SpectrallyNegativeLevy P 𝓕.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_sampling_bounded_optional_stopping_eq
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_domination_preserves_martingale_mean
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original right-continuous-filtration true martingale grid stops retain zero mean in a dominated limit. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_rightcont_sampled_martingale_bounded_grid_L1_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (f : ℝ≥0 → Ω → ℝ) (hf : Martingale f 𝓕.rightCont P)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ))
    (σ : Ω → WithTop ℕ) (τk : ℕ → Ω → WithTop ℕ)
    (hσ : IsStoppingTime 𝓖 σ)
    (hτ : ∀ k, IsStoppingTime 𝓖 (τk k))
    (hle : ∀ k, σ ≤ τk k)
    (N : ℕ) (hbdd : ∀ k ω, τk k ω ≤ (N : WithTop ℕ))
    (M B : Ω → ℝ)
    (hMkMeas : ∀ k, AEStronglyMeasurable
      (fun ω => stoppedValue (fun i : ℕ => f (e i)) (τk k) ω) P)
    (hMMeas : AEStronglyMeasurable M P)
    (hBInt : Integrable B P)
    (hDom : ∀ k, ∀ᵐ ω ∂P,
      ‖stoppedValue (fun i : ℕ => f (e i)) (τk k) ω‖ ≤ B ω)
    (hLimitBound : ∀ᵐ ω ∂P, ‖M ω‖ ≤ ‖B ω‖)
    (hAs : ∀ᵐ ω ∂P,
      Tendsto (fun k => stoppedValue (fun i : ℕ => f (e i)) (τk k) ω)
        atTop (𝓝 (M ω)))
    (hBase : (∫ ω, stoppedValue (fun i : ℕ => f (e i)) σ ω ∂P) = 0) :
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by sorry
