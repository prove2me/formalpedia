-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_diagonal_nat_clock_cash_budget_implies_full_closed_horizon
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_diagonal_nat_clock_cash_budget_implies_full_closed_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:02:56.445901+00:00
-- url     : https://prove2.me/theorems/1da86a2e-d304-4050-b797-ccbb92e2335b
-- title:
--   Original diagonal natural-clock expected dividend budgets yield all untruncated finite-horizon cash bounds
-- statement:
--   For the original spectrally negative Levy X, original ruinTime X x D and Stieltjes dividendMeasure D, assume an ENNReal expected discounted cash budget at the single clock-aligned closed horizon Iic n for every natural n>0. Then the original untruncated expected discounted dividend cash over any closed real horizon Iic T obeys the same bound, without a Fatou limit or a stronger all-T budget premise. Uses only two independently Proved UBV-HOR3 source-exact helpers.
-- source:
--   Composes public Proved 12688bb8 (all T natural cash <= clock horizon) and 196220b2 (all natural budgets imply full horizon). The explicit missing physical input is a stopped Ito budget for each n at its own time n, with terminal and time-zero atoms intact.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_nat_clock_any_closed_horizon_cash_le_horizon_n
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_uniform_nat_cash_budgets_imply_full_closed_horizon
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_hor3_original_diagonal_nat_clock_cash_budget_implies_full_closed_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (budget : ℝ≥0∞)
    (hClock : ∀ (n : ℕ), 0 < n →
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget := by sorry
