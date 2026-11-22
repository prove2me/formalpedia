-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_restricted_negative_mark_proved_sources_for_original
-- name    : AvramDividend.Classical.avram_bridge20261122_restricted_negative_mark_proved_sources_for_original
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:48:49.383746+00:00
-- url     : https://prove2.me/theorems/f43fdb1c-17a6-4e1e-9ea3-938924343c4d
-- title:
--   Original finite-activity stopped reward with genuine overshooting negative-mark generator and compensator tools
-- statement:
--   Original finite-activity stopped reward with genuine overshooting negative-mark generator and compensator tools. The original source theorem process, dividend strategy, clock and cash/terminal conclusion remain intact. The conditional child imports published exact source lemmas. For the negative-mark model, generator identities require additional finite-measure negative support beyond the finite-activity hypothesis; the result remains restricted to that case. The missing original stochastic stopped budget stays Open.
-- source:
--   Actual connected Avram parent 5a2609ae-a4a3-4f70-a863-4d08729990c5 and Proved original source heads 06353082-6d1f-4c0b-9dcc-13f881af93f8, fd7be614-84f3-404d-90a6-65cd02559e6b, d82f6b91-a816-4061-8e02-19592261e7c1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_bridge20261122_restricted_negative_mark_proved_sources_for_original
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxpos : 0 < x)
    (k : ℕ) (hk : 0 < k)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hCashI : Integrable Cash P)
    (hNuNonzero : X.ν ≠ 0) (hFiniteCap : C ≠ ⊤)
    (hRestrictedNegativeMarkSources : (∀ (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSupport : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z ≤ -2)
    (q : ℝ) (m : ℕ) (t : ℕ → ℝ≥0) (y weight : ℕ → ℝ)
    (hy : ∀ i ∈ Finset.range m, 0 ≤ y i ∧ y i ≤ (1 / 5 : ℝ))
    (hw : ∀ i ∈ Finset.range m, 0 ≤ weight i),
(∑ i ∈ Finset.range m, Real.exp (-(q * (t i : ℝ))) * weight i *
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
          (y i) z ∂X.ν)) ≤ 0) ∧
      (∀ (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSupport : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z ≤ -2)
    (m : ℕ) (y weight : ℕ → ℝ)
    (hy : ∀ i ∈ Finset.range m, 0 ≤ y i ∧ y i ≤ (1 / 5 : ℝ))
    (hw : ∀ i ∈ Finset.range m, 0 ≤ weight i),
(∑ i ∈ Finset.range m, weight i *
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
          (y i) z ∂X.ν)) =
      -(X.ν (Iio (0 : ℝ))).toReal *
        (∑ i ∈ Finset.range m, weight i * (1 + y i + y i ^ 2))) ∧
      (∀ (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSupport : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z ≤ -2)
    (hMass : 0 < (X.ν (Iio (0 : ℝ))).toReal)
    (y : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5),
(∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand
        (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
        y z ∂X.ν) < 0)) :
    MeasurableSet {ω : Ω | τ ω ≠ 0} ∧
    Integrable (fun ω => Term ω + Cash ω) P ∧
    (∫ ω in {η : Ω | τ η ≠ 0}, Term ω + Cash ω ∂P) ≤
      w x * (P {η : Ω | τ η ≠ 0}).toReal := by sorry
