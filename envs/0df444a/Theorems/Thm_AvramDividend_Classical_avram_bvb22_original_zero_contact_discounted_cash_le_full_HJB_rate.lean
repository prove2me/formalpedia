-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_contact_discounted_cash_le_full_HJB_rate
-- name    : AvramDividend.Classical.avram_bvb22_original_zero_contact_discounted_cash_le_full_HJB_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:52:56.192929+00:00
-- url     : https://prove2.me/theorems/91d1e73f-7ff8-4583-a06a-5f3c300d65db
-- title:
--   Original finite-activity zero-contact discounted Stieltjes cash bounded by full physical HJB intensity allowance
-- statement:
--   On every original finite-activity physical no-negative-jump path that survives the whole horizon and remains at zero reserve, the exact discounted Stieltjes cash is at most the origin HJB rate times the discounted length of the same physical horizon. Uses the Proved original weighted cash identity and the Proved origin drift ceiling. The negative-jump intensity allowance stays present at reserve zero and no open-interior-grid equality is asserted.
-- source:
--   Proved 32c4779c original zero-contact weighted cash equality and Proved 933ee9aa finite-activity origin HJB drift ceiling, Avram-Palmowski-Pistorius Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_nojump_zero_contact_weighted_cash_prefix
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb22_original_zero_contact_discounted_cash_le_full_HJB_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      (T : ℝ≥0∞) < ruinTime X x D ω →
      (∀ u : ℝ≥0, u ≤ T → riskProcess X x D u ω = 0) →
      (∀ u : ℝ≥0, u ∈ Ioc (0 : ℝ≥0) T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal ((q + (X.ν (Iio (0 : ℝ))).toReal) * w 0) *
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ))
      := by sorry
