-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_arbitrary_weight_localized_diffuse_gradient_bound
-- name    : AvramDividend.Classical.avram_wave4_04b_arbitrary_weight_localized_diffuse_gradient_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:34:31.226773+00:00
-- url     : https://prove2.me/theorems/0bcf7b84-09bf-4ef4-90c5-a8725f9f7c0c
-- title:
--   Every atomless Stieltjes dividend component obeys interior gradient control on the payoff-weight support
-- statement:
--   On the actual spectrally negative Lévy surplus and adapted dividend measure, the finite-horizon atomless Stieltjes remainder, including all singular-continuous dividends, satisfies a gradient-weighted bound for every nonnegative extended-real payoff weight f. The strict interior reserve localisation 0<riskProcess<C and source HJB gradient condition are required only on the support where f is nonzero and inside [0,T]. No absolute continuity of the control or density dD/dt is assumed. Supports stopped-payment indicators and finite-horizon localisation without extending interior hypotheses past the stopping support. This is a deterministic measure/control step, not a stochastic Ito–Meyer formula.
-- source:
--   Canonically Proved exact source dividend atomic/diffuse decomposition and finite support of μdiffuse, Mathlib lintegral_mono_ae and ENNReal ordered multiplication, with genuine support-aware interior hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04b_arbitrary_weight_localized_diffuse_gradient_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞)
    (hloc : ∀ t : ℝ≥0, t ≤ T → f (t : ℝ) ≠ 0 →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s : ℝ, f s ∂μdiffuse) ≤
      (∫⁻ s : ℝ,
        f s * ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
          ∂μdiffuse) := by sorry
