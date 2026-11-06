-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_oscillating_closed_crossing_cash_tendsto_horizon_atom
-- name    : AvramDividend.Classical.avram_bv_env3_original_oscillating_closed_crossing_cash_tendsto_horizon_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:37:38.883649+00:00
-- url     : https://prove2.me/theorems/f01118ec-97c3-4505-9785-6849e784c358
-- title:
--   Original closed crossing-cell cash on an oscillating grid converges to the exact horizon atom
-- statement:
--   For the original discounted dividend measure, a possibly oscillating sequence of left-grid endpoints converging to the horizon T strictly from below has right-closed crossing-cell cash tending exactly to the permitted T-payment singleton. Uses the independently Proved oscillating strict-cell vanishing theorem and Proved closed-cell decomposition. The T atom remains on surviving paths and is zero only if the original stopped clock has already expired.
-- source:
--   Fully Proved original oscillating strict-cell theorem avram_bv_env3_original_oscillating_strict_crossing_cell_cash_tendsto_zero and Proved original closed-cell split 6703a750; pinned Mathlib Filter.Tendsto.add. Avram, Palmowski and Pistorius (2007), Proposition 4(i), equation (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_oscillating_closed_crossing_cash_tendsto_horizon_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (nhds (T : ℝ)))
    (hbelowA : ∀ n, a n < (T : ℝ))
    (b : ℕ → ℝ) (hb : Monotone b)
    (hbelowB : ∀ n, b n < (T : ℝ))
    (hblim : Tendsto b atTop (nhds (T : ℝ))) :
    Tendsto (fun n =>
      ∫⁻ t in paymentTimes σ ∩ Ioc (a n) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds
        (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by sorry
