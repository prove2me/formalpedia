-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_infiniteactivity_finitecap_strict_prehorizon_cash_budget
-- name    : AvramDividend.Classical.avram_wave8_04_original_BV_infiniteactivity_finitecap_strict_prehorizon_cash_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T08:36:27.20677+00:00
-- url     : https://prove2.me/theorems/f856aa77-08ee-403c-980a-d6e2280866ef
-- title:
--   Original BV finitecap infinite-jump every strict prehorizon HJB cash+terminal expected budget
-- statement:
--   Genuine original bounded-variation, finite-cap, infinite-negative-jump-activity strictly-prehorizon expected HJB cash+survival terminal upper budget for EVERY positive deterministic horizon r strictly less than T. The exact right-open paymentTimes∩Iio(r) Stieltjes cash and original original-path reserve riskProcess at r are used, with no physical raw prepayment mesh assumption. The all-cap BV HJB/generator/gradient, no-positive-jump Lévy process, admissibility, and hJump assumptions are preserved. Proved avram_ga_a566_BV_infinite_activity_prehorizon_Fatou_to_full_T shows that this hPre bound yields the true full-T strict cash expected budget; Proved avram_p3_bv_strict_to_closed_signed_expected then supplies right-closed cash and postpayment terminal after the already Proved original strict L1 lemma. This theorem isolates the genuine remaining stochastic prehorizon generator/compensation obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_wave8_04_original_BV_infiniteactivity_finitecap_strict_prehorizon_cash_budget
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
    (hActivity : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ (r : ℝ≥0), 0 < r → (r : ℝ) < T →
      (∫⁻ ω, ENNReal.ofReal
        ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
         (if (r : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * (r : ℝ))) * w (riskProcess X x D r ω)
          else 0)) ∂P) ≤ ENNReal.ofReal (w x) := by sorry
