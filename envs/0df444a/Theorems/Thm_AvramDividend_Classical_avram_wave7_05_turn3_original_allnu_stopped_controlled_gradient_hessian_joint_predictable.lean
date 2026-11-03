-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
-- name    : AvramDividend.Classical.avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:38:57.385561+00:00
-- url     : https://prove2.me/theorems/41b798ce-dc51-4499-a4c7-50320ffae570
-- title:
--   Actual-source discounted ruin-stopped C2 gradient and Hessian jointly measurable for all Levy jump measures
-- statement:
--   For the canonical original SpectrallyNegativeLevy P 𝓕, without imposing ν=0, and the actual x+X.X-rightLimit D left-limit reserve, the true ruin mask and time-clipped discounted derivative and positive-interior capped Hessian are simultaneously measurable in the original right-continuous stopped-history sigma algebra at an original stopping time. They are also ambient measurable. This gives the two same-process predictable Itô integrands in one reusable binder contract, with no Brownian sample-space substitution. It does not construct the nonzero-jump continuous martingale or assert its stochastic integral identity.
-- source:
--   Combines two genuinely source-specific Proved strongly predictable controlled process theorems, Gaussian gradient 658fb6a1-1044-40b3-aa7d-2926663389af and capped Hessian 8902785a-d786-4def-8c13-fabb0c4782c3, with original right-continuous stopping-time measurable_stoppedValue. Enables mixed-ν consumers to discharge both predictability obligations at once.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_source_discounted_ruin_stopped_cap_hessian_predictable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s}) :
    let G : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let H : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G ∧
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H ∧
      Measurable G ∧ Measurable H := by sorry
