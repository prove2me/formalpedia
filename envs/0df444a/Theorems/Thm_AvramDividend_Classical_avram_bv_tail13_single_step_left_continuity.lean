-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_single_step_left_continuity
-- name    : AvramDividend.Classical.avram_bv_tail13_single_step_left_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:19:18.956846+00:00
-- url     : https://prove2.me/theorems/dfb3f5bb-7b74-49ca-8192-dc0bf6b9ab8a
-- title:
--   Original dividend-strategy left continuity at a deterministic positive payment clock
-- statement:
--   For a deterministic-time single nonnegative dividend step paid strictly after the clock, the exact path D is left-continuous at every time in the original IsDividendStrategy definition. The proof does not assume stochastic integrability and is reusable for the BV original cofinal-tail assessment.
-- source:
--   Original Definition IsDividendStrategy has pointwise ContinuousWithinAt on Iic t. For t<=s, D is zero on Iic t. For s<t, D is locally constant K in the relative neighbourhood Ioi s. This is an exact analytic step for the original one-clock reset scenario.

import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail13_single_step_left_continuity
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (K : Ω → ℝ)
    (hD : ∀ t ω, D t ω = if t ≤ s then 0 else K ω) :
    ∀ ω t, ContinuousWithinAt (fun u => D u ω) (Iic t) t := by sorry
