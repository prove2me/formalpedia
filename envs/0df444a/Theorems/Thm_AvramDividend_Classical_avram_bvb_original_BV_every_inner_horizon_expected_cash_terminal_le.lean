-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_original_BV_every_inner_horizon_expected_cash_terminal_le
-- name    : AvramDividend.Classical.avram_bvb_original_BV_every_inner_horizon_expected_cash_terminal_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T08:24:23.921102+00:00
-- url     : https://prove2.me/theorems/6c98cbc3-05ac-4dc9-b9bc-1c8e50f7f8a2
-- title:
--   Every BV strict inner-horizon cash and surviving terminal expectation is within initial reward
-- statement:
--   For each positive physical horizon T and each integer n, under the original bounded-variation spectrally negative Levy process, positive cap, admissible original dividends, HJB generator and slope inequalities, and original right-dividend and nonnegative-reward conditions, the expected actual strict pre-ruin discounted dividend cash before T-T/(n+2) plus the surviving original postpayment terminal reward at T is at most w(x). The proof requires an original same-filtration stopped chronological Stieltjes and compensated Levy ledger, zero-contact accounting, infinite-activity first-moment tail and ruin/horizon atoms. The theorem is a true fixed-inner-horizon source budget and imports no global raw HJB drift L1 hypothesis. It implies the parent uniform positive expected gap limit directly.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_original_BV_every_inner_horizon_expected_cash_terminal_le
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
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    ∀ n : ℕ, (∫ ω, F n ω ∂P) ≤ w x := by sorry
