-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route10_original_BV_positive_error_fatou_witness
-- name    : AvramDividend.Classical.avram_route10_original_BV_positive_error_fatou_witness
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T14:17:49.535895+00:00
-- url     : https://prove2.me/theorems/4612f9a8-667b-4d4a-bbeb-a718576be597
-- title:
--   Original stopped BV physical-grid positive-error signed Fatou witness for strict horizon cash and terminal
-- statement:
--   For the actual stopped bounded-variation spectrally-negative Lévy dividend strategy, construct on one physical-grid family nonnegative measurable integrable finite-grid cash witnesses, an integrable centred compensated jump source, a pointwise nonpositive HJB drift, and positive approximation errors with vanishing L1 mean. Prove the actual strict pre-horizon dividend payment and surviving pre-right-payment terminal payoff is bounded by the Fatou liminf of the same grid witnesses. Includes nonnegative original terminal payoff. Unlike stronger c1e2f021 does not demand an L1 combined signed drift residual or zero approximation error per grid.
-- source:
--   Original BV physical-grid cash/terminal source reduction for canonical a19d8b28, composed with accepted d3f3db15 signed-Fatou and 78fa7075 strict-payoff L1. Physical source inputs: 166eef1c HJB residual sign, 71cd4e89 jump identity, 4956c00b weighted raw jump, BV-ERROR7 positive-error convergence. Still a deep original-process mathematical obligation.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route10_original_BV_positive_error_fatou_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Y : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    (0 ≤ᵐ[P] Y) ∧
    ∃ F M B E : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (E n ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (E n ω) 0 ∂P) atTop (nhds (0 : ℝ)) ∧
      (∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + M n ω + B n ω + max (E n ω) 0) ∧
      (∀ᵐ ω ∂P,
        ENNReal.ofReal (Y ω) ≤
          liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by sorry
