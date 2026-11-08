-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_cash_grid_discounted_upper
-- name    : AvramDividend.Classical.avram_p3_2_original_strict_cash_grid_discounted_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:37:42.435931+00:00
-- url     : https://prove2.me/theorems/61b7e0a6-2b57-4365-bfdd-0f526725abf7
-- title:
--   Original strict stopped cash and time-zero atom bounded by the discounted physical-grid envelope
-- statement:
--   The original strict-pre-horizon dividend cash, including time-zero right-limit payout, is bounded by the left-end discounted physical grid envelope already proved on the actual paymentTimes.
-- source:
--   Source-exact strict-versus-unfiltered original paymentTimes comparison and the previously accepted original finite stopped discounted cash upper sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_cash_mesh_le_unfiltered
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_stopped_discounted_cash_sum_upper

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_strict_cash_grid_discounted_upper
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
    (ENNReal.ofReal (rightLimit D 0 ω) +
      ∑ i ∈ Finset.range n,
        (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩
              Iio (T : ℝ)) ∩ Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ≤
      ENNReal.ofReal (rightLimit D 0 ω) +
      ∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Ioc (u i : ℝ) (u (i + 1) : ℝ),
            (1 : ℝ≥0∞) ∂(dividendMeasure D ω)):= by sorry
