-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top15_original_zero_nu_ruin_clipped_strict_expected_upper
-- name    : AvramDividend.Classical.avram_ubv_gauss_top15_original_zero_nu_ruin_clipped_strict_expected_upper
-- status  : Open
-- author  : @WillR
-- created : 2026-11-09T10:17:22.176052+00:00
-- url     : https://prove2.me/theorems/d65c7756-5bce-4c06-8b48-fba923fedc34
-- title:
--   Original zero-jump Gaussian ruin-clipped strict stopped reward has expected upper bound
-- statement:
--   This is the genuinely missing expectation conjunct of c63d897f on the actual zero-jump Gaussian process, original dividend strategy, and genuine right-continuous ruin-clipped stopping times. It asserts that the zero-clock-masked discounted prepayment terminal plus strict-before-stop Stieltjes cash has expectation no larger than the initial candidate w(x). The already Proved d9020a5d supplies L1 independently. The mathematical proof must construct the original stopped C2 Ito/Stieltjes HJB supermartingale estimate, including time-zero right payment, positive ruin prepayment contact, continuous dividend mass and the final stop-straddling cell.
-- source:
--   Necessary source-exact expectation-only reduction of parent c63d897f-ed1b-465f-a542-bcc39fa65ca5; parent bridge uses Proved d9020a5d and 6b7a13a0 for L1, with this child for the expected bound. hNuZero, original X/D, 𝓕.rightCont, strict Iio cash, time-zero/ruin conventions, and top cap are retained.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss_top15_original_zero_nu_ruin_clipped_strict_expected_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
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
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k, (∫ ω,
      if σ k ω = 0 then w x else
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal ∂P) ≤ w x := by sorry
