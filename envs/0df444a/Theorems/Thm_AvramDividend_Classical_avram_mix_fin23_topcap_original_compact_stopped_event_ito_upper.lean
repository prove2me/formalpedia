-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin23_topcap_original_compact_stopped_event_ito_upper
-- name    : AvramDividend.Classical.avram_mix_fin23_topcap_original_compact_stopped_event_ito_upper
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T10:32:03.074993+00:00
-- url     : https://prove2.me/theorems/304898c7-8b2c-4a90-9afb-b9ead77b06b3
-- title:
--   Original finite-jump mixed top-cap compact stopped Itô initial-event upper
-- statement:
--   The irreducible top-cap analytic obligation remaining after physical clock geometry and compact reward L1 are separated. Under finite negative jump activity, nonzero intrinsic Gaussian variance, standing assumptions and HJB, for any original-filtration bounded ruin-clipped stopping sequence with original process sample values bounded by j+1, show the exact stopped terminal-plus-inclusive-dividend reward is measurable and its expectation on each right-continuous time-zero event and positive-clock mask is at most w(x) times probability of the original physical positive-clock mask. Use an honest stopped Ito-Meyer and martingale localisation, treating the initial right dividend, strict pre-ruin cash, ruin and horizon atoms, and avoiding a global L1 cross-noise or unjustified large-mark first-moment assumption. This supplies the only analytic input to c087c2cb.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin23_topcap_original_compact_stopped_event_ito_upper
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
    (hCtop : C = ⊤) (κ : ℕ → Ω → ℝ≥0)
    (hκstop : ∀ j, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ j ω : WithTop ℝ≥0)))
    (hκle : ∀ j ω, κ j ω ≤ σ ω)
    (hκbound : ∀ j ω, X.X (κ j ω) ω ≤ (j : ℝ) + 1)
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ j ω, H j ω =
      Real.exp (-(q * (κ j ω : ℝ))) *
        w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
        else riskProcess X x D (κ j ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    (∀ j, Measurable (H j)) ∧
    ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      ∀ j, (∫ ω in A ∩ {η : Ω | κ j η ≠ 0}, H j ω ∂P) ≤
        w x * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal := by sorry
