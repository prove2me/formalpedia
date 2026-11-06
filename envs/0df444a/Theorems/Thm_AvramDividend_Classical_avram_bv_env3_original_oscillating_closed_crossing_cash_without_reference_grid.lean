-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_oscillating_closed_crossing_cash_without_reference_grid
-- name    : AvramDividend.Classical.avram_bv_env3_original_oscillating_closed_crossing_cash_without_reference_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:44:46.781203+00:00
-- url     : https://prove2.me/theorems/1c314392-092f-47a2-9db5-5a55a1fe3c3b
-- title:
--   Original closed crossing-cell cash converges to the exact horizon atom without reference-grid assumptions
-- statement:
--   For any possibly oscillating original physical-grid sequence a_n approaching T strictly from below, original discounted stopped cash in the right-closed crossing cell (a_n,T] tends to exactly the original T-payment singleton. No auxiliary reference sequence is required, and the surviving-path horizon atom is preserved.
-- source:
--   Fully Proved no-reference oscillating strict-cell theorem and fully Proved original closed-cell atom decomposition 6703a750. Avram, Palmowski and Pistorius (2007), Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_oscillating_closed_crossing_cash_without_reference_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (nhds (T : ℝ)))
    (hbelow : ∀ n, a n < (T : ℝ)) :
    Tendsto (fun n =>
      ∫⁻ t in paymentTimes σ ∩ Ioc (a n) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds
        (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by sorry
