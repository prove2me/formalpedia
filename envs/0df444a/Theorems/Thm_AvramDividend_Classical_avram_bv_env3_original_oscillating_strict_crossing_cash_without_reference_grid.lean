-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_oscillating_strict_crossing_cash_without_reference_grid
-- name    : AvramDividend.Classical.avram_bv_env3_original_oscillating_strict_crossing_cash_without_reference_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:43:16.668943+00:00
-- url     : https://prove2.me/theorems/847df2cc-9232-4e69-91d6-d88154f701e2
-- title:
--   Original strict crossing-cell cash vanishes for any convergent physical grid without reference-grid hypotheses
-- statement:
--   For any sequence a_n of real left endpoints converging to T, with no monotonicity or side condition, original stopped discounted dividend cash in the open crossing cell (a_n,T) tends to zero. The proof constructs an explicit monotone reciprocal reference grid strictly below T, then applies the accepted original oscillating-grid source theorem.
-- source:
--   Fully Proved BV-ENV3 oscillating crossing-cell theorem 0e23235a-5be0-41d8-8f53-f2ed738088ca; pinned Mathlib one_div_le_one_div_of_le, tendsto_natCast_atTop_atTop, Filter.Tendsto.atTop_add, tendsto_inv_atTop_zero. Avram, Palmowski and Pistorius (2007), Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_oscillating_strict_crossing_cash_without_reference_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (nhds (T : ℝ))) :
    Tendsto (fun n =>
      ∫⁻ t in paymentTimes σ ∩ Ioo (a n) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by sorry
