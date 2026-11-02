-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_gradient_gaussian_integrable_mean_zero
-- name    : AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_gradient_gaussian_integrable_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:10:23.025058+00:00
-- url     : https://prove2.me/theorems/2f6c2a71-eaf3-4af3-9c93-0cd881af9726
-- title:
--   Discounted ruin-stopped original Gaussian gradient cell is integrable and exactly centred under bounded localisation
-- statement:
--   For the original spectrally negative Levy process with zero jump measure and arbitrary sigma including sigma=0, fix an admissible dividend strategy. The actual strict pre-dividend left-limit gradient, multiplied by exponential discount and the inclusive true ruin-survival and deterministic finite-horizon masks, is strongly predictable in the original right-continuous filtration. At a bounded right-continuous stopping time, assume the resulting original stopped gradient weight H is bounded by K. Then the real source drift-centred increment Y=X.X_(tau+h)-X.X_tau-hc is L2 and L1; H*Y is integrable and has exact expectation zero. This supplies the actual finite-cell stopped Gaussian martingale contribution, without changing probability space or introducing a separate Brownian process. It is not a general-jump continuous bracket theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_gradient_gaussian_integrable_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K) :
    let H : Ω → ℝ := stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let Y : Ω → ℝ := fun ω =>
        X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    Integrable (fun ω => H ω * Y ω) P ∧
      (∫ ω, H ω * Y ω ∂P) = 0 := by
  sorry
