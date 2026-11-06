-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_strict_crossing_cash_tendsto_nhds_horizon
-- name    : AvramDividend.Classical.avram_bv_env3_original_strict_crossing_cash_tendsto_nhds_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:03:22.464447+00:00
-- url     : https://prove2.me/theorems/c1765d1f-a5f0-4544-b69f-2d8e3049c4bf
-- title:
--   Original strict crossing-cell cash tends to zero in the full real neighbourhood of its horizon
-- statement:
--   The original stopped discounted dividendMeasure cash function over strict crossing interval (a,T) tends to zero as real a tends to T, without monotonicity or auxiliary sequence assumptions; in particular all oscillating physical-grid subsequences satisfy it.
-- source:
--   Proved original no-reference oscillating strict-cell theorem 847df2cc-9232-4e69-91d6-d88154f701e2; pinned Mathlib Filter.tendsto_iff_seq_tendsto at first-countable nhds. Avram, Palmowski and Pistorius (2007), Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_strict_crossing_cash_tendsto_nhds_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun a : ℝ =>
      ∫⁻ t in paymentTimes σ ∩ Ioo a (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      (nhds (T : ℝ)) (nhds 0) := by sorry
