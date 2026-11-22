-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_UBV_original_source_given_clipped_finitegrid_HJB_controls
-- name    : AvramDividend.Classical.avram_bridge20261122_UBV_original_source_given_clipped_finitegrid_HJB_controls
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:13:04.846969+00:00
-- url     : https://prove2.me/theorems/06740f72-9dcc-4a1c-a886-1197cea97e1d
-- title:
--   Original UBV five-witness stopped Ito source conditional on physically specialised clipped finite-grid and integral HJB bounds
-- statement:
--   The unchanged original UBV process, stopped surplus and dividend Cash/Term and five-witness signed Ito bound; additionally assumes two authentic HJB nonpositivity controls for this exact X,x,D,w,C,q: finite clipped signed-rate mesh and integral over a source-physical measure. The residual full stopped Ito-Meyer decomposition and reward inequality remain open. The parent derives both added premises from already-Proved source theorems.
-- source:
--   Original connected public stopped Itô source fdb9a6a3 and Proved original clipped generator finite-grid 6594404b plus integral 77668e88, with their Proved imported dependencies.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bridge20261122_UBV_original_source_given_clipped_finitegrid_HJB_controls
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
    (hPhysicalClippedHJB : (∀ (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (r : ℝ≥0 × Ω → ℝ) (hr : ∀ p, 0 ≤ r p)
    {ι : Type*} (s : Finset ι) (p : ι → ℝ≥0 × Ω)
    (Δ : ι → ℝ) (hΔ : ∀ i ∈ s, 0 ≤ Δ i),
let U : ℝ≥0 × Ω → ℝ := fun z =>
      let y := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t z.2 - rightLimit D t z.2) z.1
      if y ∈ Icc δ K then y else δ
    ∑ i ∈ s, Δ i *
      (Real.exp (-(q * ((p i).1 : ℝ))) *
        ((X.generator w (U (p i)) - q * w (U (p i))) +
          r (p i) * (1 - deriv w (U (p i))))) ≤ 0) ∧
      (∀ (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (r : ℝ≥0 × Ω → ℝ) (hr : ∀ p, 0 ≤ r p)
    (μ : Measure (ℝ≥0 × Ω)),
let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
      if y ∈ Icc δ K then y else δ
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        ((X.generator w (U p) - q * w (U p)) +
          r p * (1 - deriv w (U p)))
    Integrable H μ → (∫ p, H p ∂μ) ≤ 0)) :
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
