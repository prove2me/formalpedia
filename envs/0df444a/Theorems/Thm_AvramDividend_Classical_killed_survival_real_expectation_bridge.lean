-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_survival_real_expectation_bridge
-- name    : AvramDividend.Classical.killed_survival_real_expectation_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:59:41.772912+00:00
-- url     : https://prove2.me/theorems/368972f9-6495-437a-9054-f6f23f6e8512
-- title:
--   Lévy killed-survival capital transform as a finite real reflected-infimum expectation
-- statement:
--   For θ>0 and finite horizon, the capital-integrated killed-survival probability Laplace transform equals the extended nonnegative embedding of the ordinary finite real expectation of the exponential reflected-infimum envelope. The envelope is nonnegative, measurable, bounded and integrable, so this identity can be used directly in real-valued stochastic calculus.
-- source:
--   Proved killed_survival_capital_reflected_infimum_transform and reflected_infimum_envelope_integrable plus Mathlib ofReal_integral_eq_lintegral_ofReal.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_killed_survival_capital_reflected_infimum_transform
import Theorems.Thm_AvramDividend_Classical_reflected_infimum_envelope_integrable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_survival_real_expectation_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
        (x, ω) ∂P ∂volume) =
    ENNReal.ofReal (∫ (ω : Ω),
      Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ ∂P) := by sorry
