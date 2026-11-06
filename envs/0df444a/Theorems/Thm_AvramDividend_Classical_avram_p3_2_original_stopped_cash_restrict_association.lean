-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_cash_restrict_association
-- name    : AvramDividend.Classical.avram_p3_2_original_stopped_cash_restrict_association
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:07:55.444905+00:00
-- url     : https://prove2.me/theorems/aaae1ec1-6950-4ccd-88ca-57dfc98ae14e
-- title:
--   Original dividendMeasure stopped-cell restriction associative identity
-- statement:
--   The original stopped Stieltjes cash integral over actual paymentTimes intersected with an Ioc mesh cell equals the integral over that Ioc cell for dividendMeasure first restricted to the original paymentTimes, for every ENNReal integrand.
-- source:
--   Pinned Mathlib Measure.restrict_restrict for measurable Ioc; interchange the payment-set and cell intersections and rewrite exact original dividendMeasure integrals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_stopped_cash_restrict_association
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ≥0) (m i : ℕ) (f : ℝ → ℝ≥0∞) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
      f t ∂(dividendMeasure D ω)) =
    (∫⁻ t in Ioc (u i : ℝ) (u (i + 1) : ℝ),
      f t ∂((dividendMeasure D ω).restrict
        (paymentTimes (ruinTime X x D ω)))):= by sorry
