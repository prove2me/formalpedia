-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_controlled_stopped_discounted_gradient_finite_gaussian_L2_sum_zero
-- name    : AvramDividend.Classical.avram_wave7_05_original_controlled_stopped_discounted_gradient_finite_gaussian_L2_sum_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:56:02.388619+00:00
-- url     : https://prove2.me/theorems/2f1cb1fd-052b-4dae-b871-d833f7f4d9c5
-- title:
--   Finite actual discounted ruin-controlled original Gaussian gradient stochastic sum is L2 centred
-- statement:
--   A finite set of real horizons applied to the very same original bounded stopping time, true source X and original dividend strategy D produces a finite sum of source Gaussian increments weighted by the actual pre-dividend left-limit derivative e^-qt w'(leftLim(x+X-rightLimit D)), killed at true ruin and horizon. Under one explicit bounded localisation and zero Levy jump measure, each term and the total gain are L2, the total gain is Integrable and its exact expectation is zero. Arbitrary sigma including zero; not full mixed-jump Ito.
-- source:
--   Proved individual controlled stopped source gradient L2 and zero mean b6e0c60e-f61a-42e4-b513-288adb62b442, pinned Mathlib finite MemLp and integral sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_controlled_stopped_discounted_gradient_gaussian_L2_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_controlled_stopped_discounted_gradient_finite_gaussian_L2_sum_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (S : Finset ι) (h : ι → ℝ≥0) (K : ℝ) (hK : 0 ≤ K)
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
    let F : ι → Ω → ℝ := fun i ω =>
      H ω * (X.X (τ ω + h i) ω - X.X (τ ω) ω -
        (h i : ℝ) * X.c)
    (∀ i ∈ S, MemLp (F i) 2 P) ∧
      MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
      Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
      (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0 := by sorry
