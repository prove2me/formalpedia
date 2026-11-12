-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a07_topcap_original_ito_cash_initial_condexp_bound
-- name    : AvramDividend.Classical.avram_a07_topcap_original_ito_cash_initial_condexp_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T17:07:53.334589+00:00
-- url     : https://prove2.me/theorems/e83a72d7-5b15-4517-9d14-99fc4614cc9c
-- title:
--   Original ruin-clipped top-cap stopped cash conditional HJB upper bound
-- statement:
--   Prove the exact source-level original ruin-clipped discounted cash HJB budget as a conditional expectation given the time-zero right-continuous filtration. The Gaussian and compensated small-band original martingale witnesses are explicit premises; handle dividend contact, stochastic Ito drift, discount, ruin and horizon atoms. The conclusion is sufficient to construct a centred stopped reward residual without assuming an independent martingale representation.
-- source:
--   Physical conditional-expectation core of A07 top-cap, a necessary HJB consequence without assuming closed two-noise majorant.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a07_topcap_original_ito_cash_initial_condexp_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
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
    (n : ℕ) (hn : 0 < n)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCtop : C = ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRadapt : ∀ t : ℝ≥0,
      AEStronglyMeasurable[𝓕.rightCont t] (R t) P)
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (hRbracket : ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2)
    (hJstopped :
      ∃ Jsmall : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
          Tendsto
            (fun k : ℕ =>
              avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
            atTop (nhds (Jsmall t ω))) ∧
        (∀ t : ℝ≥0, Integrable (Jsmall t) P) ∧
        (∀ s t : ℝ≥0, s ≤ t →
          ∀ᵐ ω ∂P,
            condExp (𝓕.rightCont s) P (Jsmall t) ω = Jsmall s ω) ∧
        Integrable (fun ω => Jsmall (σ ω) ω) P ∧
        (∀ᵐ ω ∂P,
          condExp (𝓕.rightCont 0) P
            (fun ω => Jsmall (σ ω) ω) ω = 0)) :
    ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ w x := by sorry
