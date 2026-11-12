-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a07_topcap_original_eventwise_measurable_budget
-- name    : AvramDividend.Classical.avram_a07_topcap_original_eventwise_measurable_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T15:59:39.350071+00:00
-- url     : https://prove2.me/theorems/94b3efa8-6729-4e8f-8195-79961ff5f291
-- title:
--   Original top-cap stopped reward positive-clock eventwise budget and measurability
-- statement:
--   Establish measurability of the original capped stopping time and the physical stopped reward, together with the initial sigma-algebra eventwise expected HJB upper bound restricted to strictly positive stopping times for top cap C=⊤. This source-exact stochastic Ito-Meyer obligation suffices for the top-cap spatial localisation existential theorem, using a constant top spatial cutoff, avoiding artificial processes.
-- source:
--   Original stopped Ito-Meyer verification on the original Lévy probability space and right-continuous filtration; reduction from c087c2cb-0d29-4169-a0c7-34d34febe362.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a07_topcap_original_eventwise_measurable_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (n : ℕ) (hn : 0 < n) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ ω) ω - rightLimit D (σ ω) ω
        else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCtop : C = ⊤) :
    Measurable σ ∧ Measurable F ∧
      ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A ∩ {η : Ω | σ η ≠ 0}, F ω ∂P) ≤
        w x * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal := by sorry
