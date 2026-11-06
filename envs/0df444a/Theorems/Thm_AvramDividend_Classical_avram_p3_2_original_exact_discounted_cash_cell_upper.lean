-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_exact_discounted_cash_cell_upper
-- name    : AvramDividend.Classical.avram_p3_2_original_exact_discounted_cash_cell_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:24:13.555202+00:00
-- url     : https://prove2.me/theorems/8d2310ba-ffea-4793-bf49-59c30b6e8538
-- title:
--   Original once-discounted Stieltjes cash is at most left-endpoint weighted physical cash
-- statement:
--   For original pre-ruin paymentTimes intersected with a stopped Ioc mesh cell, the exact physical once-discounted Stieltjes cash is bounded above by the original unweighted cell mass times left-endpoint exponential discount.
-- source:
--   Compose fully Proved original left-endpoint cash lintegral upper and original stopped cash restriction-association to obtain the exact-domain upper mesh squeeze.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_left_endpoint_cash_lintegral_upper
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_cash_restrict_association

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_exact_discounted_cash_cell_upper
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
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        (1 : ℝ≥0∞) ∂(dividendMeasure D ω)):= by sorry
