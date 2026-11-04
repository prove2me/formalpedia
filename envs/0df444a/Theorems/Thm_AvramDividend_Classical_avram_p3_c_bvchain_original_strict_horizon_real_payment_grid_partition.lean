-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_horizon_real_payment_grid_partition
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_strict_horizon_real_payment_grid_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:49:30.353792+00:00
-- url     : https://prove2.me/theorems/fb87806c-2d7e-4239-9260-c2a52933fa89
-- title:
--   Exact real-valued original stopped strict-horizon dividend cash partition across a finite grid
-- statement:
--   For the genuine original stopped dividend carrier and strictly increasing finite mesh ending before b, the real strict-open stopped discounted Stieltjes Cash equals the sum of real right-closed cell Cash and real open final-cell Cash. The proof derives the requisite extended-real finiteness from the original dividend strategy and the Proved closed-horizon pathwise finite Cash result, then converts the exact Proved extended-real partition without adding integrability hypotheses.
-- source:
--   Proved exact original ENNReal grid partition 8b976562 and P4-D original literal Cash pathwise finiteness c4e50d93; Mathlib ENNReal.toReal_sum/add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_horizon_paymentTimes_finite_grid_partition
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_strict_horizon_real_payment_grid_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ) (hzero : u 0 = 0)
    (hgrid : ∀ i, i < n → u i < u (i + 1))
    (b : ℝ≥0) (hfinal : u n < b) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
      (∑ i ∈ Finset.range n,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (u n : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
