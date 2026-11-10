-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_finite734_finite_activity_original_cofinal_prefix_expected_source
-- name    : AvramDividend.Classical.avram_bv_finite734_finite_activity_original_cofinal_prefix_expected_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-09T07:40:50.919193+00:00
-- url     : https://prove2.me/theorems/3f849360-e048-4089-9338-bcd545f74344
-- title:
--   Finite-activity physical cofinal strict-prefix expected HJB source for original capped BV dividends
-- statement:
--   Only unresolved original stochastic source for 8271cf4d: establish a genuinely refining cofinal family of clocks strictly below T at which the true arbitrary admissible-D discounted Stieltjes cash plus the SAME fixed surviving T terminal satisfies the expected HJB upper bound. The accepted Proved bridge 28343e2d converts precisely these source budgets to 8271cf4d without any generator-B global L1 or arbitrary nonrefining grids. Strict u_n<T prevents choosing the final T as every prefix. Includes time-zero right payment, zero reserve, cap contact, negative jumps and ruin chronology. Original Ω,P,𝓕,X,D throughout; no independent model.
-- source:
--   BV-FIN734 physical source reduction using Proved 28343e2d-7a82-4210-846d-a6af569b97be, 9 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_finite734_finite_activity_original_cofinal_prefix_expected_source
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤)
    (hactivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ u : ℕ → ℝ,
      Monotone u ∧
      (∀ n, 0 ≤ u n) ∧
      (∀ n, u n < T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) ∧
      (∀ n,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
           else 0) ∂P) ≤ w x) := by sorry
