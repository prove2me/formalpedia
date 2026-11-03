-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_controlled_stopped_gaussian_exact_variance
-- name    : AvramDividend.Classical.avram_wave7_05_turn3_original_controlled_stopped_gaussian_exact_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:22:47.806183+00:00
-- url     : https://prove2.me/theorems/6a3514b2-24ca-4f94-9129-5c76f9065077
-- title:
--   Actual ruin-stopped discounted controlled Gaussian gradient gain has exact sigma-squared variance
-- statement:
--   The exact source on its original Ω, P and right-continuous filtration, with ν=0 and arbitrary Gaussian parameter σ, has a bounded localised predictable derivative integrand evaluated at the left limit of x+X-rightLimit D, discounted and killed at the true ruin time. Its actual source stopped centred gain lies in physical L2 and its square is integrable; its expected square equals the integral of the same actual controlled integrand squared times hσ². This is a source-specific coefficient identity, not a mixed-ν Itô theorem.
-- source:
--   Direct source-faithful specialisation of proved Wave3 controlled derivative predictability (658fb6a1-1044-40b3-aa7d-2926663389af), proved controlled L2 stopped gain (b6e0c60e-f61a-42e4-b513-288adb62b442), and proved original source stopped weighted Gaussian isometry (4294d18f-9e1d-43e0-a67a-c123a1438800).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_controlled_stopped_discounted_gradient_gaussian_L2_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn3_original_controlled_stopped_gaussian_exact_variance
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
      Integrable (fun ω => (H ω * Y ω) ^ 2) P ∧
      (∫ ω, (H ω * Y ω) ^ 2 ∂P) =
        (∫ ω, (H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2) := by sorry
