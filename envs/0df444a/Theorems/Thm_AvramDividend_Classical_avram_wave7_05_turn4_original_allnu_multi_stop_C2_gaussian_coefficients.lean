-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_multi_stop_C2_gaussian_coefficients
-- name    : AvramDividend.Classical.avram_wave7_05_turn4_original_allnu_multi_stop_C2_gaussian_coefficients
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:53:22.476469+00:00
-- url     : https://prove2.me/theorems/186c0d87-955f-47c7-a5c2-35002ba40cd8
-- title:
--   Arbitrary-jump original-source finite-stop controlled Gaussian C2 coefficient predictability and energy measurability
-- statement:
--   On the exact original source with arbitrary nu, a finite family of genuine right-continuous original stopping times has both true ruin-killed, discounted left-reserve derivative and clipped second derivative measurable in their corresponding stopped sigma fields, and the finite sums of derivative, Hessian and their square localisation energy are ambient measurable.
-- source:
--   Proved original all-nu gradient and Hessian same-stop strong predictability 41b798ce-dc51-4499-a4c7-50320ffae570, indexed by genuine source stops; no assumption ν=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn4_original_allnu_multi_stop_C2_gaussian_coefficients
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0) (S : Finset ι)
    (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s}) :
    let G : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
    let H : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
    (∀ (i : ι) (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (G i) ∧
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (H i)) ∧
    Measurable (fun ω => ∑ i ∈ S, G i ω) ∧
    Measurable (fun ω => ∑ i ∈ S, H i ω) ∧
    Measurable (fun ω => Finset.sum S (fun i => (G i ω) ^ 2 + (H i ω) ^ 2)) := by sorry
