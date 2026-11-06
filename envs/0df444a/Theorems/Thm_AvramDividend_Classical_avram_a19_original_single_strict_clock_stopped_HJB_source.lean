-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_original_single_strict_clock_stopped_HJB_source
-- name    : AvramDividend.Classical.avram_a19_original_single_strict_clock_stopped_HJB_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T00:17:30.812344+00:00
-- url     : https://prove2.me/theorems/51b72610-16ac-4bf7-b81e-ab1b6456a6a7
-- title:
--   Actual original BV stopped HJB expected budget at one arbitrary strict clock
-- statement:
--   For each deterministic nonnegative observation clock s strictly before positive T, prove the source-specific original spectrally negative BV Lévy expected HJB upper bound for literal strict Stieltjes dividends up to s plus the true T-survival terminal payoff. The source contains no mesh limit or cofinality requirement. The standing generator, gradient, cap, admissibility, ruin and secant assumptions remain exact.
-- source:
--   Fixed-clock original stochastic kernel of public cofinal source a233906b. A sorry-free reduction from a233906b can apply this bound at u(n) for each n. This is the minimal unresolved true controlled Lévy HJB expectation source; the deterministic clock selection is independently proved ef6585cb.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_original_single_strict_clock_stopped_HJB_source
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
    ∀ s : ℝ, 0 ≤ s → s < T →
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio s,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x := by sorry
