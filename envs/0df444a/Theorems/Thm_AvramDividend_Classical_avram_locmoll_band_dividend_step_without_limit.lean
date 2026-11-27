-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_dividend_step_without_limit
-- name    : AvramDividend.Classical.avram_locmoll_band_dividend_step_without_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:12:12.755983+00:00
-- url     : https://prove2.me/theorems/26046577-5352-401a-93c1-5e0820265669
-- title:
--   Physical dividend cell ledger, integrable envelope and exact grid integral before passage to the limit
-- statement:
--   Physical dividend cell ledger, integrable envelope and exact grid integral before passage to the limit
-- source:
--   Physical dividend step certificate 45e95e97-eef3-4a02-ab5a-913134e1d165

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_dividend_step_without_limit
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
    ∀ ω, ∃ (a b c : ℕ → ℝ → ℝ) (K : ℝ),
      let μ := (dividendMeasure D ω).restrict
        (paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ))
      let A : ℝ → ℝ := fun t => riskProcess X x D t.toNNReal ω
      let B : ℝ → ℝ := fun t => x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω
      let E : ℝ → ℝ := fun t => Real.exp (-(q * t))
      let F : ℕ → ℝ → ℝ := fun n t => E t - c n t * Q (a n t) (b n t)
      (∀ n t, t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ) →
        (t = 0 → a n t = x ∧ b n t = x - rightLimit D 0 ω ∧ c n t = 1) ∧
        (0 < t → ∃ i < k n,
          let l := min (u n i) (θ ω)
          let r := min (u n (i + 1)) (θ ω)
          (l : ℝ) < t ∧ t ≤ (r : ℝ) ∧
          a n t = x + X.X r ω - rightLimit D l ω ∧
          b n t = (if r = θ ω ∧ ¬ (r = 0 ∨ (r : ℝ≥0∞) < ruinTime X x D ω)
            then riskProcess X x D r ω else x + X.X r ω - rightLimit D r ω) ∧
          c n t = E (r : ℝ))) ∧
      (∀ᵐ t ∂μ, B t ≤ A t ∧ ∀ n, b n t ≤ a n t) ∧
      (∀ n, AEStronglyMeasurable (F n) μ) ∧
      Integrable (fun _ : ℝ => K) μ ∧
      (∀ n, ∀ᵐ t ∂μ, ‖F n t‖ ≤ K) ∧
      (∀ n, Dividend n ω + Cash ω = ∫ t, F n t ∂μ) := by sorry
