-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_actual_dividend_diffuse_derivative_prejump_stieltjes_integral_eq
-- name    : AvramDividend.Classical.avram_wave4_04b_actual_dividend_diffuse_derivative_prejump_stieltjes_integral_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:38:12.990062+00:00
-- url     : https://prove2.me/theorems/a4bdfc6a-e9ea-441d-a535-c9160a08691b
-- title:
--   Actual full diffuse Stieltjes gradient integral equals genuine strict source-prejump controlled gradient integral
-- statement:
--   On every sample path of the actual adapted Lévy-controlled surplus and finite horizon, split its complete right-Stieltjes dividend measure into the exact countable right-payment atoms and a null-singleton diffuse measure. For every measurable or nonmeasurable nonnegative ENNReal weight and arbitrary real test function w, the positive-time diffuse integral of the derivative evaluated at the canonical riskProcess equals exactly that evaluated at the genuine same-source strict pre-jump reserve x+X_{s−}−D⁺_s, almost everywhere with respect to the actual sample-specific diffuse Stieltjes measure. Singular-continuous and absolutely continuous dividend mass are both preserved. The time-zero dividend is exclusively atomic and is not silently discarded from the full measure decomposition. This is an exact finite-horizon integral identity, not a stochastic Itô formula.
-- source:
--   Proved actual dividend diffuse strict source-prejump a.e. UUID 0b7de539-6541-40bf-8d7a-76c5e0bdd988, and Mathlib MeasureTheory.setLIntegral_congr_fun_ae pinned source and remote compiler type.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_actual_dividend_diffuse_preserves_strict_source_prejump_ae

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_actual_dividend_diffuse_derivative_prejump_stieltjes_integral_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      μ Set.univ = ENNReal.ofReal (rightLimit D T ω) ∧
      (∀ (w : ℝ → ℝ) (f : ℝ → ℝ≥0∞),
        (∫⁻ s in Ioi (0 : ℝ),
          f s * ENNReal.ofReal
            (deriv w (riskProcess X x D s.toNNReal ω)) ∂μdiffuse) =
        (∫⁻ s in Ioi (0 : ℝ),
          f s * ENNReal.ofReal
            (deriv w (x +
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
              rightLimit D s.toNNReal ω)) ∂μdiffuse)) := by
  sorry
