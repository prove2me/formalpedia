-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_finiteactivity_finitecap_strict_horizon_expected_budget
-- name    : AvramDividend.Classical.avram_wave8_04_original_BV_finiteactivity_finitecap_strict_horizon_expected_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T12:12:21.951574+00:00
-- url     : https://prove2.me/theorems/9c7c13e9-7927-47ef-9ddf-a97dce1ee812
-- title:
--   Original finite-cap BV finite-activity true strictly truncated horizon expected HJB cash plus terminal
-- statement:
--   True original bounded-variation finite-negative-activity finite-cap strict closed-at-start, open-at-horizon Iio T cash plus original reserve positive-survivor terminal expected budget. All original Standing, Levy process, admissible dividend strategy, HJB and derivative inequality, nonnegative pre-ruin candidate and hJump are unchanged. This is the precise remaining finite-activity stochastic proof obligation after the established Proved strict reward integrability lemma and Proved strict-to-right-closed signed endpoint bridge. Its conclusion is exactly the strict analogue of the published finite-cap true horizon source; no raw-w prepayment source or false mesh-limit is assumed. It can be approached via the server-Proved original finite-activity compensated B mean (5f0c926f) and integrable F-B (cfb04e7d), followed by a sound one-sided source error transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_wave8_04_original_BV_finiteactivity_finitecap_strict_horizon_expected_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) (hFinite : C ≠ ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let S : ℝ≥0 := ⟨T,hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x := by sorry
