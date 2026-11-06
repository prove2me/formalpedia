-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_strict_crossing_cell_discounted_cash_tendsto_zero
-- name    : AvramDividend.Classical.avram_bv_env3_original_strict_crossing_cell_discounted_cash_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:05:31.456697+00:00
-- url     : https://prove2.me/theorems/28ff0f1f-f253-4128-b019-a2df18206090
-- title:
--   Original stopped dividend strict crossing-cell discounted cash vanishes under physical-grid exhaustion
-- statement:
--   For an original admissible dividend strategy and a monotone sequence of real left-grid endpoints approaching a fixed nonnegative horizon, the discounted Stieltjes mass in the strictly open final cell tends to zero, including exact strict paymentTimes stopping. This is the continuity-from-above step needed to separate the final physical-grid crossing cell from any right-horizon singleton atom, without assuming the T atom disappears.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), equation (5.13); original payment measure finite-horizon source c4e50d93-76bf-4771-9e5f-5ffeba198952; pinned Mathlib lintegral_tendsto_of_tendsto_of_antitone. Distinct from P3-GRID4 secant sign and canonical c877. Bridge: decompose Ioc(a_n,T) into Ioo(a_n,T) and singleton {T}.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_strict_crossing_cell_discounted_cash_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q)
    (a : ℕ → ℝ) (ha : Monotone a)
    (hlim : Tendsto a atTop (nhds (T : ℝ))) :
    Tendsto (fun n =>
      ∫⁻ t in paymentTimes σ ∩ Ioo (a n) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by sorry
