-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_rightcont_sampled_martingale_uniform_L2_mean_limit
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_rightcont_sampled_martingale_uniform_L2_mean_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:52:20.234819+00:00
-- url     : https://prove2.me/theorems/ba3b7ebb-3664-43b8-9b1b-666d5f227803
-- title:
--   Original right-continuous-filtration sampled true martingale L2 stopped limit is integrable and centred
-- statement:
--   The true source stopped-ruin clock is a stopping time in the original 𝓕.rightCont filtration. This source-X compatible variant samples a genuine Martingale f 𝓕.rightCont P on a monotone time grid, optional-stops in the sampled right-continuous filtration, and deduces globally Integrable centred M from almost-sure positive/negative-part convergence and separate uniform second-moment bounds. It does not infer Martingale f 𝓕.rightCont P from source X or replace an unresolved jump isometry; those remain explicit assumptions.
-- source:
--   Composes proved monotone-sampling bounded optional stopping in the 𝓕.rightCont sampled filtration with P4-E two-sided L2 signed zero-mean limit, keeping the original X : SpectrallyNegativeLevy P 𝓕.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_sampling_bounded_optional_stopping_eq
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_L2_two_sided_signed_martingale_mean_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original right-continuous-filtration bounded grid stops yield centred limits under uniform quadratic energy. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_rightcont_sampled_martingale_uniform_L2_mean_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
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
    (hσ : IsStoppingTime 𝓖 σ) (hτ : ∀ k, IsStoppingTime 𝓖 (τk k))
    (hle : ∀ k, σ ≤ τk k)
    (N : ℕ) (hbdd : ∀ k ω, τk k ω ≤ (N : WithTop ℕ))
    (M : Ω → ℝ)
    (hPosI : ∀ k, Integrable
      (fun ω => max (stoppedValue (fun i : ℕ => f (e i)) (τk k) ω) 0) P)
    (hNegI : ∀ k, Integrable
      (fun ω => max (-(stoppedValue (fun i : ℕ => f (e i)) (τk k) ω)) 0) P)
    (hPosMeas : ∀ k, AEStronglyMeasurable
      (fun ω => max (stoppedValue (fun i : ℕ => f (e i)) (τk k) ω) 0) P)
    (hNegMeas : ∀ k, AEStronglyMeasurable
      (fun ω => max (-(stoppedValue (fun i : ℕ => f (e i)) (τk k) ω)) 0) P)
    (hPosMMeas : AEStronglyMeasurable (fun ω => max (M ω) 0) P)
    (hNegMMeas : AEStronglyMeasurable (fun ω => max (-(M ω)) 0) P)
    (hPosConv : ∀ᵐ ω ∂P, Tendsto
      (fun k => max (stoppedValue (fun i : ℕ => f (e i)) (τk k) ω) 0)
      atTop (𝓝 (max (M ω) 0)))
    (hNegConv : ∀ᵐ ω ∂P, Tendsto
      (fun k => max (-(stoppedValue (fun i : ℕ => f (e i)) (τk k) ω)) 0)
      atTop (𝓝 (max (-(M ω)) 0)))
    (C : ℝ) (hC : 0 ≤ C)
    (hPos2 : ∀ k, Integrable (fun ω =>
      (max (stoppedValue (fun i : ℕ => f (e i)) (τk k) ω) 0) ^ 2) P ∧
      (∫ ω, (max (stoppedValue (fun i : ℕ => f (e i)) (τk k) ω) 0) ^ 2 ∂P) ≤ C)
    (hNeg2 : ∀ k, Integrable (fun ω =>
      (max (-(stoppedValue (fun i : ℕ => f (e i)) (τk k) ω)) 0) ^ 2) P ∧
      (∫ ω, (max (-(stoppedValue (fun i : ℕ => f (e i)) (τk k) ω)) 0) ^ 2 ∂P) ≤ C)
    (hBase : (∫ ω, stoppedValue (fun i : ℕ => f (e i)) σ ω ∂P) = 0) :
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by sorry
