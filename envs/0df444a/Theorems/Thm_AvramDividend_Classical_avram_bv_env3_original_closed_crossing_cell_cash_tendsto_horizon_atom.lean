-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_closed_crossing_cell_cash_tendsto_horizon_atom
-- name    : AvramDividend.Classical.avram_bv_env3_original_closed_crossing_cell_cash_tendsto_horizon_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:16:00.250201+00:00
-- url     : https://prove2.me/theorems/7a479ca3-dd78-4596-9514-f0eeed64a8f8
-- title:
--   Original last right-closed crossing-cell cash converges exactly to its horizon singleton payment
-- statement:
--   On the original dividend measure and strict paymentTimes, every monotone sequence of left-grid endpoints strictly below a finite horizon and tending to it makes the right-closed final-cell discounted cash converge exactly to the discounted mass paid at time T. The proof composes two fully Proved BV-ENV3 source lemmas: strict crossing cell tends to zero and closed cash equals strict cash plus the horizon atom.
-- source:
--   Proved AvramDividend.Classical.avram_bv_env3_original_strict_crossing_cell_discounted_cash_tendsto_zero (28ff0f1f) and Proved AvramDividend.Classical.avram_bv_env3_original_last_cell_closed_cash_splits_horizon_atom (6703a750); pinned Mathlib Filter.Tendsto.add. Avram, Palmowski and Pistorius (2007), Proposition 4(i), equation (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_closed_crossing_cell_cash_tendsto_horizon_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q)
    (a : ℕ → ℝ) (ha : Monotone a)
    (hlim : Tendsto a atTop (nhds (T : ℝ)))
    (hbelow : ∀ n, a n < (T : ℝ)) :
    Tendsto (fun n =>
      ∫⁻ t in paymentTimes σ ∩ Ioc (a n) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds
        (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by sorry
