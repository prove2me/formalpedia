-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_original_trueband_given_compensated_Lp2_and_gaussian_caplinear
-- name    : AvramDividend.Classical.avram_bridge20261122_original_trueband_given_compensated_Lp2_and_gaussian_caplinear
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:15:06.906901+00:00
-- url     : https://prove2.me/theorems/f801495c-2415-4261-b6b3-7ac48c740bb2
-- title:
--   True-physical-band stopped Ito-Meyer source conditional on proved compensated-small-jump Lp2 and original Gaussian cap-linear mesh interfaces
-- statement:
--   Original physical stopped five-witness Ito source with no change to the true-band stop, same X,D,ruin clock, discounted original terminal and Stieltjes cash. Conditional on the source-faithful small-jump predictable Lp2 isometry/mean-zero extension and the original Gaussian cap-linear drift/occupation upper-strip bounds, all specialised to the exact X, sample space and filtration. Still requires constructing actual compensated stochastic integrals and the stopped Ito identity.
-- source:
--   Connected Open f4ddfb50 plus two Proved small-jump L2 heads d9b76a03 and cc8d3c87 and two Gaussian physical upper-strip heads cecea733 and 776a7faa, covering both source groups by directed imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_bridge20261122_original_trueband_given_compensated_Lp2_and_gaussian_caplinear
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hBand : ∀ (K : ℝ≥0) (a b : ℕ) (hab : a ≤ b)
      (σ : Ω → WithTop ℝ≥0)
      (hσ : IsStoppingTime 𝓕.rightCont σ)
      (hσBound : ∀ ω, σ ω ≤ (K : WithTop ℝ≥0))
      (hσCount : (Set.range σ).Countable),
        let B : Set ℝ :=
          Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
        let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
          ((Measure.count.restrict {s : ℝ≥0 |
            0 < s ∧ X.X s ω -
              Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
            (fun s : ℝ≥0 => (s, X.X s ω -
              Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
        let J : Ω → ℝ := fun ω =>
          (∫ p in Ioc 0 (σ ω).untopA ×ˢ B, p.2 ∂NX ω) -
            (((σ ω).untopA : ℝ) * (∫ z in B, z ∂X.ν))
        Integrable J P ∧ (∫ ω, J ω ∂P) = 0)
    (hPredictableL2Gaussian : (∀ (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)),
(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →L[ℝ] Lp ℝ (2 : ℝ≥0∞) P)
        (hSimpleIso : ∀ v : ↥(Lp.simpleFunc ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))),
          ‖I (v : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))‖ =
          ‖(v : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))‖),
      ∀ v, ‖I v‖ = ‖v‖)) ∧
      (∀ (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)),
(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →L[ℝ] Lp ℝ (2 : ℝ≥0∞) P)
        (J : Lp ℝ (2 : ℝ≥0∞) P →L[ℝ] ℝ)
        (hSimpleZero : ∀ v : ↥(Lp.simpleFunc ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))),
          J (I (v : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) = 0),
      ∀ v, J (I v) = 0)) ∧
      (∀ (x b q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) (hq : 0 ≤ q),
let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i => x + X.X (s i + Δ) ω - rightLimit D (s i) ω
    let V : ℝ → ℝ := fun y => if y ≤ b then w y else w b + (y - b)
    let centred : ℕ → ℝ := fun i =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
    (Finset.range (m + 1)).sum (fun i =>
      if s i < ρ ∧ b < Y i ∧ b < Z i then
        e i * (V (Z i) - V (Y i) - centred i) else 0) ≤
    (Finset.range (m + 1)).sum (fun i =>
      if s i < ρ ∧ b < Y i ∧ b < Z i then
        (Δ : ℝ) * max X.c 0 else 0)) ∧
      (∀ (x b q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m : ℕ),
let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i => x + X.X (s i + Δ) ω - rightLimit D (s i) ω
    let V : ℝ → ℝ := fun y => if y ≤ b then w y else w b + (y - b)
    let centred : ℕ → ℝ := fun i =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
    (Finset.range (m + 1)).sum (fun i =>
      if b < Y i ∧ b < Z i then
        e i * (V (Z i) - V (Y i) - centred i) else 0) ≤
    (Finset.range (m + 1)).sum (fun i =>
      if b < Y i ∧ b < Z i then
        e i * (Δ : ℝ) * max X.c 0 else 0))) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω) := by sorry
