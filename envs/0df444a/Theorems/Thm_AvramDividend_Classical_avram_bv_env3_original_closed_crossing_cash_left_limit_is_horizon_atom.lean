-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_closed_crossing_cash_left_limit_is_horizon_atom
-- name    : AvramDividend.Classical.avram_bv_env3_original_closed_crossing_cash_left_limit_is_horizon_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:06:24.698308+00:00
-- url     : https://prove2.me/theorems/0a6ff798-d412-49ba-9f34-627b6ae39ccb
-- title:
--   Original closed crossing cash has the exact horizon atom as the full left-neighbourhood limit
-- statement:
--   As the real left endpoint approaches finite T from below through arbitrary values, original discounted stopped cash in (a,T] tends to exactly the permitted payment singleton at T. Holds at the complete left neighbourhood rather than only on a specified sequence.
-- source:
--   Accepted original strict crossing cash topological limit c1765d1f and original closed-cell atom identity 6703a750; pinned Mathlib self_mem_nhdsWithin. Avram, Palmowski and Pistorius (2007), Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_closed_crossing_cash_left_limit_is_horizon_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun a : ℝ =>
      ∫⁻ t in paymentTimes σ ∩ Ioc a (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      (nhdsWithin (T : ℝ) (Iio (T : ℝ)))
      (nhds (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by sorry
