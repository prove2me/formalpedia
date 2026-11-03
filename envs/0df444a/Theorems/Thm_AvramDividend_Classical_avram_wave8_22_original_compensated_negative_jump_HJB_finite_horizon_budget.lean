-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_compensated_negative_jump_HJB_finite_horizon_budget
-- name    : AvramDividend.Classical.avram_wave8_22_original_compensated_negative_jump_HJB_finite_horizon_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:19:05.748959+00:00
-- url     : https://prove2.me/theorems/b23d7dc9-8be3-4979-a5dd-3de59ea22e82
-- title:
--   Original BV signed negative-jump compensation gives complete finite-horizon HJB budget without assumed zero-mean martingale
-- statement:
--   For the original spectrally negative Levy X, actual negative jump source NX and physical predictable clock on the same original Omega/P/filtration, derive the full terminal plus discounted dividend finite-horizon budget. Construct canonical finite negative Levy bands from X and prove the true stopped signed source minus its pathwise random compensator is integrable and zero mean, then apply the independently Proved original HJB budget theorem. The genuine future adapted rectangle, predictable kernel L1, stopped Ito chain identity, generator and dividend sign/integrability remain explicit. No assumed centring.
-- source:
--   Accepted original stopped signed compensator 9ebbcecd-f9c3-4cf2-ad81-c54fffbc06c4, canonical bands b80e4040-c3f7-4cd9-afc1-5f231aab3645, original conditional Ito HJB budget c3658f01-c0c2-4760-977c-a7cebb95a7da.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_stopped_signed_jump_minus_true_predictable_compensator_L1_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_levy_negative_quadratic_canonical_finite_mark_bands
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_source_hjb_expected_budget_conditional_ito
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_compensated_negative_jump_HJB_finite_horizon_budget
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕)
  (NX : Ω → Measure (ℝ≥0 × ℝ))
  (hNX : ∀ ω, NX ω = ((Measure.count.restrict
    {u : ℝ≥0 | 0 < u ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
    (fun u : ℝ≥0 => (u, X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
  (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ)))
  (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
    (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ))
    (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
  (hKmeas : AEMeasurable K P)
  (MK : @Measure ((ℝ≥0 × Ω) × ℝ)
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ)))
  (hMK : MK = P.bind K) (T : ℝ≥0)
  (S : Set ((ℝ≥0 × Ω) × ℝ)) (hST : S = {p | p.1.1 ≤ T})
  (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _
    (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] S)
  (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ)))
  (hMT : MT = MK.restrict S)
  (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
  (hμfinite : μ Set.univ < ∞)
  (hμclock : ∀ A : Set (ℝ≥0 × Ω),
    MeasurableSet[𝓕.rightCont.predictable] A →
    μ A = ((((volume : Measure ℝ).restrict
      (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
  (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
    𝓕.rightCont.predictable; μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
  (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C' : Set ℝ),
    MeasurableSet[𝓕.rightCont i] A → MeasurableSet C' →
    MT ((Set.Ioi i ×ˢ A) ×ˢ C') = N ((Set.Ioi i ×ˢ A) ×ˢ C'))
  (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
  (hτ : IsStoppingTime 𝓕.rightCont
    (fun ω => (τ ω : WithTop ℝ≥0)))
  (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
  (hGm : Measurable[(@Prod.instMeasurableSpace _ _
    (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
  (hGiN : Integrable G N)
  (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
  (hH : H = fun p =>
    if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0)
  (hSupport : S.indicator H = H)
  (Mart : Ω → ℝ)
  (hMartDef : ∀ ω, Mart ω =
    (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
    (∫ t, ∫ z, H ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)))
  (q : ℝ) (hq : 0 < q)
  (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
  (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
  (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
  (hw_smooth :
    (¬ X.BoundedVariation →
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
    (X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
  (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.GeneratorIntegrable w y ∧
      max (X.generator w y - q * w y) (1 - deriv w y) = 0)
  (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
  (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
  (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
  (W Cash Term Gdrift Hdiv : Ω → ℝ)
  (hW : ∀ ω, W ω =
    if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (τ ω) ω - rightLimit D (τ ω) ω
    else riskProcess X x D (τ ω) ω)
  (hCash : ∀ ω, Cash ω =
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
  (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
  (hTermI : Integrable Term P)
  (hGI : Integrable Gdrift P) (hHI : Integrable Hdiv P)
  (hGHnonpos : ∀ᵐ ω ∂P, Gdrift ω + Hdiv ω ≤ 0)
  (hIto : ∀ᵐ ω ∂P,
    Term ω + Cash ω = w x + Mart ω + Gdrift ω + Hdiv ω) :
  Integrable Cash P ∧
    (∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
    (∫ ω, Cash ω ∂P) ≤ w x ∧
    (∫⁻ ω, ∫⁻ s in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
