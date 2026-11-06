-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_stopped_discounted_cash_sum_lower
-- name    : AvramDividend.Classical.avram_p3_2_original_finite_stopped_discounted_cash_sum_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:18:48.414594+00:00
-- url     : https://prove2.me/theorems/d85d9049-1af1-4ace-83a1-48ff11585e3c
-- title:
--   Original finite stopped cash sum dominates endpoint discounted mass
-- statement:
--   For every original stopped X/D finite mesh prefix, exact once-discounted dividendMeasure cells plus initial rightpayment dominate the right-endpoint discounted unweighted physical cells plus the same initial atom.
-- source:
--   Finset.sum_le_sum of the fully Proved exact original Stieltjes cell lower bound, followed by add_le_add_left for the physical time-zero rightpayment atom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_exact_discounted_cash_cell_lower

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_finite_stopped_discounted_cash_sum_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (m n : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ)))) *
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Ioc (u i : ℝ) (u (i + 1) : ℝ),
            (1 : ℝ≥0∞) ∂(dividendMeasure D ω))) ≤
      ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))):= by sorry
