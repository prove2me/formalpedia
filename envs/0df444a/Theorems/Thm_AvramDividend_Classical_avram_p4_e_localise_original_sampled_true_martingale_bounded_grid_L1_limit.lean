-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_sampled_true_martingale_bounded_grid_L1_limit
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_sampled_true_martingale_bounded_grid_L1_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:25:07.935197+00:00
-- url     : https://prove2.me/theorems/880bbd70-00a3-4597-86ac-048e65743b5c
-- title:
--   Original bounded genuine martingale grid stopping preserves zero mean through L1 localisation
-- statement:
--   Source-compatible bounded optional sampling on an increasing original-time grid gives centred finite-grid stochastic residuals from a genuine martingale. A single actual integrable random envelope and a.s. limit then yield a globally integrable, centred limit. The stopped true martingale, sampled stopping-time, uniform bound and convergence hypotheses are explicit; no local-martingale optional stopping is inferred.
-- source:
--   Original Levy process definition, pinned Mathlib OptionalStopping, proved source-compatible bounded grid sampling and P4-E dominated martingale mean transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_sampling_bounded_optional_stopping_eq
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_domination_preserves_martingale_mean
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Bounded genuine martingale grid stops preserve zero mean through a dominated L¹ limit. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_sampled_true_martingale_bounded_grid_L1_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (f : ℝ≥0 → Ω → ℝ) (hf : Martingale f 𝓕 P)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕 (e i)
         mono' := by
           intro i j hij
           exact 𝓕.mono (he hij)
         le' := by
           intro i
           exact 𝓕.le (e i) } : Filtration ℕ mΩ))
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
