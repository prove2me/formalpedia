-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_oscillating_strict_crossing_cell_cash_tendsto_zero
-- name    : AvramDividend.Classical.avram_bv_env3_original_oscillating_strict_crossing_cell_cash_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:33:19.780234+00:00
-- url     : https://prove2.me/theorems/0e23235a-5be0-41d8-8f53-f2ed738088ca
-- title:
--   Original discounted strict crossing-cell cash vanishes for an oscillating convergent physical grid
-- statement:
--   For the original discounted stopped dividend measure, the left endpoints a_n can oscillate arbitrarily as long as they tend to a fixed finite horizon T. Given any monotone reference endpoints b_n approaching T strictly from below, the strict crossing-cell integral Ioo(a_n,T) tends to zero by a pointwise set-monotonicity squeeze from the already Proved monotone-reference theorem. No stochastic or conditional HJB assertion is added. This resolves the variable-mesh monotonicity caveat for P3 physical grids.
-- source:
--   Proved original monotone crossing-cell theorem 28ff0f1f-f253-4128-b019-a2df18206090; pinned Mathlib tendsto_order and lintegral_mono_set; actual original dividendMeasure/paymentTimes. Source: Avram, Palmowski and Pistorius (2007), Proposition 4(i), equation (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_oscillating_strict_crossing_cell_cash_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (nhds (T : ℝ)))
    (b : ℕ → ℝ) (hb : Monotone b)
    (hbelow : ∀ n, b n < (T : ℝ))
    (hblim : Tendsto b atTop (nhds (T : ℝ))) :
    Tendsto (fun n =>
      ∫⁻ t in paymentTimes σ ∩ Ioo (a n) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by sorry
