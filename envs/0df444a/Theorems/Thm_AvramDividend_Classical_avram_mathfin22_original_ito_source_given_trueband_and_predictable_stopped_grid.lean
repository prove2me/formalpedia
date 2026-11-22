-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_ito_source_given_trueband_and_predictable_stopped_grid
-- name    : AvramDividend.Classical.avram_mathfin22_original_ito_source_given_trueband_and_predictable_stopped_grid
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T19:44:38.960022+00:00
-- url     : https://prove2.me/theorems/193fbc06-a888-45ee-8e94-bdaaf7b923cf
-- title:
--   Original stopped Ito-Meyer source given source-proved true Lévy band and bounded predictable stopped finite-grid martingales
-- statement:
--   Public original stopped Ito-Meyer source residual conditional on both mathematically substantive original physical Lévy-process martingale certificates already independently proved or being closed: (i) exact compensated true z-weighted all-activity reciprocal negative-band stochastic integral integrability and centring at each bounded countably-valued right-continuous stopping time; (ii) exact original stopped predictable bounded finite-grid compensated signed simple negative-mark sum integrability and centring. Every original Avram source hypothesis and five-witness conclusion of root-connected canonical fdb9a6a3 remains unchanged; the two additional hypotheses state the physical NX, ν, actual stopping mask and predictable coefficients verbatim. This child is an honest Open obligation for the original stopped Gaussian, full predictable Itô-Meyer, dividend Stieltjes and generator-residual pathwise inequality. The source branch will be connected by a SKETCH_ACCEPTED proof of parent f4ddfb50 with the existing first certificate and the genuine second certificate f17bb762, then through an already SKETCH_ACCEPTED fdb9 -> f4dd original mission graph edge to the Avram root. No synthetic PRM, global finite negative jump rate, or circular source assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mathfin22_original_ito_source_given_trueband_and_predictable_stopped_grid
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
    (hPredictableGrid : ∀ {ι : Type*} [DecidableEq ι]
      (F : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ F, s i < t i)
    (S : ι → Set ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i))
    (hNeg : ∀ i ∈ F, S i ⊆ Iio (0 : ℝ))
    (hν : ∀ i ∈ F, X.ν (S i) < ⊤)
    (g : ι → SimpleFunc ℝ ℝ)
    (H : ι → Ω → ℝ)
    (hH : ∀ i ∈ F,
      StronglyMeasurable[𝓕.rightCont (s i)] (H i))
    (K : ι → ℝ)
    (hBound : ∀ i ∈ F, ∀ ω, ‖H i ω‖ ≤ K i)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ),
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ι → ℝ → Set ℝ := fun i y => S i ∩ (g i) ⁻¹' {y}
    let G : ι → Ω → ℝ := fun i ω =>
      ∑ y ∈ (g i).range, y *
        ((NX ω (Ioc (s i) (t i) ×ˢ B i y)).toReal -
          ((((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i y))).toReal)
    let W : ι → Ω → ℝ := fun i ω =>
      if τ ω ≤ (s i : WithTop ℝ≥0)
        then 0 else H i ω
    Integrable (fun ω => ∑ i ∈ F, W i ω * G i ω) P ∧
        (∫ ω, ∑ i ∈ F, W i ω * G i ω ∂P) = 0) :
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
