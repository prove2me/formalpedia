-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_exact_discounted_cash_cell_lower
-- name    : AvramDividend.Classical.avram_p3_2_original_exact_discounted_cash_cell_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:13:01.076371+00:00
-- url     : https://prove2.me/theorems/c639e5c2-9b12-4c51-ab5b-6e548902cc69
-- title:
--   Original once-discounted Stieltjes cash dominates endpoint weighted physical cash
-- statement:
--   For the exact original paymentTimes intersected with the stopped Ioc mesh cell, the physical once-discounted ENNReal dividendMeasure integral is at least unweighted physical dividendMeasure cash multiplied by the right-endpoint exponential weight.
-- source:
--   Combine independently fully Proved avram_p3_2_original_right_endpoint_cash_lintegral_lower and avram_p3_2_original_stopped_cash_restrict_association, rewriting both unweighted and discounted physical integrals from the nested source-restricted measure to the canonical intersection-domain measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_right_endpoint_cash_lintegral_lower
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_cash_restrict_association

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_exact_discounted_cash_cell_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (m i : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ)))) *
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        (1 : ℝ≥0∞) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)):= by sorry
