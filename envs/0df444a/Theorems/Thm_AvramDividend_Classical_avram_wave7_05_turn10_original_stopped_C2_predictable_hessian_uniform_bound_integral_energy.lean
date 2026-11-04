-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_stopped_C2_predictable_hessian_uniform_bound_integral_energy
-- name    : AvramDividend.Classical.avram_wave7_05_turn10_original_stopped_C2_predictable_hessian_uniform_bound_integral_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:57:11.234418+00:00
-- url     : https://prove2.me/theorems/93eb878a-736c-4706-8550-70f5c3bf6fab
-- title:
--   Original stopped C2 predictable reserve Hessian with uniform pointwise cap has bounded integrated quadratic energy
-- statement:
--   For canonical original SpectrallyNegativeLevy X on its original probability space and filtration, the predictable stopped and interior-localised second derivative at the true controlled reserve is Borel measurable. If the Hessian integrand is uniformly capped by K, its square is integrable with expectation at most K squared, enabling Hessian martingale-bracket localisation without independent Brownian constructions.
-- source:
--   Proved original-source stopped joint gradient/Hessian predictability, canonical riskProcess and ruinTime; pointwise quadratic domination under probability measure.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn10_original_stopped_C2_predictable_hessian_uniform_bound_integral_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n ω ≤ s})
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ n, H n = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n ω : WithTop ℝ≥0)))
    (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ n ω, |H n ω| ≤ K) :
    ∀ n, Integrable (fun ω => H n ω * H n ω) P ∧
      (∫ ω, H n ω * H n ω ∂P) ≤ K ^ 2 := by sorry
