-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_sampled_true_martingale_uniform_L2_mean_limit
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_sampled_true_martingale_uniform_L2_mean_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:25:20.154789+00:00
-- url     : https://prove2.me/theorems/685d3857-3a26-41ca-93ad-5a433e076091
-- title:
--   Original true martingale bounded grid stops yield centred L1 limit from uniform L2 energy
-- statement:
--   On the same native Levy probability law, a true original-time martingale sampled on a monotone grid and stopped at bounded genuine grid stopping times has centred samples by certified optional stopping. Uniform positive and negative quadratic moment controls and a.s. convergence yield a globally integrable zero-mean limit without common pathwise domination. No local-martingale theorem is presumed.
-- source:
--   Source Levy structure, Proved chat01 bounded sampled optional-stopping equality and Proved P4-E two-sided uniform second-moment limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_sampling_bounded_optional_stopping_eq
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_L2_two_sided_signed_martingale_mean_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True bounded grid stops and two-sided L² energy preserve centred original-source limits. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_sampled_true_martingale_uniform_L2_mean_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
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
