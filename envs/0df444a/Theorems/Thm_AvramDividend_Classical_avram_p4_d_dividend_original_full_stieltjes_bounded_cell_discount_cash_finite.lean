-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_bounded_cell_discount_cash_finite
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_bounded_cell_discount_cash_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:02:57.198028+00:00
-- url     : https://prove2.me/theorems/25d579ae-a331-4c85-b3dd-1180a8486463
-- title:
--   Original bounded-horizon exact Stieltjes discounted cash cell is finite
-- statement:
--   For every source-original admissible dividend strategy and finite horizon T, the exact discounted Stieltjes cash integral over any cell (a,b] with b≤T is finite. The original Stieltjes cell mass is bounded by closed-horizon measure mass, which a previously proved source theorem identifies with ENNReal.ofReal of the finite real rightLimit D T. The exact discount is at most one; no absolute continuity or atomlessness is required. This is a concrete finiteness bridge for canonical stopped Cash.toReal.
-- source:
--   Proved source dividendMeasure_Icc_zero_eq_rightLimit and original exact discounted Stieltjes cell sandwich

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_exact_discount_cell_endpoint_sandwich

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_bounded_cell_discount_cash_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (a b T : ℝ≥0) (hbT : b ≤ T) :
    (∫⁻ u in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) < ⊤ := by sorry
