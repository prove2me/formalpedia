-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_dividend_secant_integral_exact
-- name    : AvramDividend.Classical.avram_locmoll_band_dividend_secant_integral_exact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T23:40:42.866879+00:00
-- url     : https://prove2.me/theorems/b980c2dc-b50f-4bb4-b148-7f7a2859258e
-- title:
--   The limiting physical secant integral is exactly diffuse residual plus all eligible right-payment residuals
-- statement:
--   The limiting physical secant integral is exactly diffuse residual plus all eligible right-payment residuals
-- source:
--   Physical Stieltjes integral route to 8b646752-f25d-4029-9771-dda1d287c7e1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_dividend_secant_integral_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (C : ℝ≥0∞) (hC : 0 < C)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (δ R : ℝ) (hδ : 0 < δ) (hδx : δ < x) (hxR : x < R)
    (θ : Ω → ℝ≥0)
    (hθle : ∀ ω, θ ω ≤ T.toNNReal)
    (hprefix : ∀ ω t, t < θ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc δ R)
    (hstop : IsStoppingTime 𝓕.rightCont (fun ω => (θ ω : WithTop ℝ≥0)))
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hNonneg : ∀ y : ℝ, 0 ≤ g y)
    (hZero : ∀ y : ℝ, y ≤ 0 → g y = 0)
    (hGrad : ∀ y : ℝ, δ ≤ y → 1 ≤ deriv g y)
    (hGen : ∀ y : ℝ, δ ≤ y → ENNReal.ofReal y ≤ C →
      X.GeneratorIntegrable g y ∧ X.generator g y - q * g y ≤ 0)
    (hSec : ∀ a b : ℝ, δ ≤ b → b ≤ a →
      a - b ≤ g a - g b)
    (hLoss : ∀ a b : ℝ, 0 ≤ b → b ≤ a →
      a - b ≤ g a - g b + δ)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    let Cash : Ω → ℝ := (fun ω : Ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    let G : Ω → ℝ := (fun ω : Ω => ∫ t in Ioc (0 : ℝ) (θ ω : ℝ),
      Real.exp (-(q * t)) *
        (X.generator g (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal) -
          q * g (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal)))
    let Term : Ω → ℝ := fun ω => Real.exp (-(q * (θ ω : ℝ))) *
      g (if θ ω = 0 ∨ (θ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (θ ω) ω - rightLimit D (θ ω) ω
        else riskProcess X x D (θ ω) ω)
    let J : Ω → ℝ≥0 → ℝ := fun ω s =>
      if s ≤ θ ω ∧ (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) then
        Real.exp (-(q * (s : ℝ))) *
          ((rightLimit D s ω - D s ω) +
            g (x + X.X s ω - rightLimit D s ω) - g (riskProcess X x D s ω))
      else 0
    let Diff : Ω → ℝ := fun ω =>
      ∫ t in (paymentTimes (ruinTime X x D ω) ∩ Ioc (0 : ℝ) (θ ω : ℝ)),
        Real.exp (-(q * t)) *
          (1 - deriv g (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal))
        ∂((dividendMeasure D ω).restrict
          {t : ℝ | rightLimit D t.toNNReal ω = D t.toNNReal ω})
    let u : ℕ → ℕ → ℝ≥0 := fun n i => (i : ℝ≥0) * T.toNNReal / ((m n : ℝ≥0) + 1)
    let k : ℕ → ℕ := fun n => m n + 1
    let Source : ℕ → Ω → ℝ := fun n ω =>
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (θ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      ∑ i ∈ Finset.range (k n),
        ((E (v (i + 1)) - E (v i)) * g (Y (v i)) +
          E (v (i + 1)) * (g (Z i) - g (Y (v i))))
    let Dividend : ℕ → Ω → ℝ := fun n ω =>
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (θ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      let pre : Prop := θ ω = 0 ∨ (θ ω : ℝ≥0∞) < ruinTime X x D ω
      (g (x - rightLimit D 0 ω) - g x) +
        (∑ i ∈ Finset.range (k n),
          ((E (v (i + 1)) - E (v i)) * g (Y (v i)) +
            E (v (i + 1)) * (g (Z i) - g (Y (v i))) +
            E (v (i + 1)) *
              (g (riskProcess X x D (v (i + 1)) ω) - g (Z i)) +
            E (v (i + 1)) *
              (g (Y (v (i + 1))) -
                g (riskProcess X x D (v (i + 1)) ω)))) +
        (if pre then 0 else E (θ ω) *
          (g (riskProcess X x D (θ ω) ω) - g (Y (θ ω)))) -
        Source n ω
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    ∀ ω,
      let μ := (dividendMeasure D ω).restrict
        (paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ))
      (∫ t, Real.exp (-(q * t)) *
        (1 - Q (riskProcess X x D t.toNNReal ω)
          (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω)) ∂μ) =
        Diff ω + ∑' s : ℝ≥0, J ω s := by sorry
