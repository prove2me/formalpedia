-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_controlled_stopped_discounted_gradient_gaussian_L2_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_original_controlled_stopped_discounted_gradient_gaussian_L2_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:50:36.543023+00:00
-- url     : https://prove2.me/theorems/b6e0c60e-f61a-42e4-b513-288adb62b442
-- title:
--   Actual discounted ruin-controlled original Gaussian derivative martingale cell is L2 and centred
-- statement:
--   For actual X on the original Ω and filtration and the same original dividend strategy D, the predictable derivative of the pre-dividend left-limit reserve x+X-rightLimit D, discounted and killed inclusively at real ruin and clipped at finite horizon, multiplies a genuine zero-jump stopped Gaussian source increment. Under a bounded coefficient localisation, this exact source product is MemLp 2 and Integrable, and its expectation is zero. This strengthens existing original controlled L1 cell to L2, without any detached Brownian model or a claim for general nonzero jump measure.
-- source:
--   Proved original-source strongly predictable control gradient 658fb6a1-1044-40b3-aa7d-2926663389af, Proved generic bounded source Gaussian L2 zero mean 8cf2614f-c9fe-47f1-896a-57969706c910.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_controlled_stopped_discounted_gradient_gaussian_L2_mean_zero
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
    MemLp (fun ω => H ω * Y ω) 2 P ∧
      Integrable (fun ω => H ω * Y ω) P ∧
        (∫ ω, H ω * Y ω ∂P) = 0 := by sorry
