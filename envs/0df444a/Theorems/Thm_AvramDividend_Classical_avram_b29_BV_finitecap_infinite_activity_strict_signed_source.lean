-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b29_BV_finitecap_infinite_activity_strict_signed_source
-- name    : AvramDividend.Classical.avram_b29_BV_finitecap_infinite_activity_strict_signed_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T15:13:37.336009+00:00
-- url     : https://prove2.me/theorems/b6244155-8d3e-4c01-8ab7-e3556b512770
-- title:
--   Infinite-activity original BV finite-cap strictly cofinal physical signed cash source
-- statement:
--   The genuine original bounded-variation finite-cap, infinite-negative-jump-activity strict signed physical-grid certificate. Construct cofinal pre-horizon physical times, nonpositive-mean compensated signed source gains, integrable vanishing positive error and the original strict Iio dividend cash plus terminal survival payoff under infinite negative Lévy activity. This is the complementary case to the finite-activity B29 obligation; no finite jump enumeration may be used. Source-negative jump band and compensation limits remain substantive.
-- source:
--   Avram B28 physical BV finite-cap source certificate d022c4c7, Protter finite variation Itô and stopped compensation, 15 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_b29_BV_finitecap_infinite_activity_strict_signed_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (hwpos : 0 < w x)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∃ u : ℕ → ℝ,
      Monotone u ∧
      (∀ n, 0 ≤ u n) ∧
      (∀ n, u n < T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) ∧
      ∃ R J Err : ℕ → Ω → ℝ,
        (∀ n, Integrable (fun ω => R n ω + J n ω) P ∧
          (∫ ω, R n ω + J n ω ∂P) ≤ 0) ∧
        (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
        Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P)
          atTop (𝓝 (0 : ℝ)) ∧
        (∀ n, ∀ᵐ ω ∂P,
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
           else 0) ≤
            w x + (R n ω + J n ω) + max (Err n ω) 0)  := by sorry
