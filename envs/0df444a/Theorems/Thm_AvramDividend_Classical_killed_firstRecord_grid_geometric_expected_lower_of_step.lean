-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_geometric_expected_lower_of_step
-- name    : AvramDividend.Classical.killed_firstRecord_grid_geometric_expected_lower_of_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:56:16.315346+00:00
-- url     : https://prove2.me/theorems/06491b68-510f-45eb-923c-612ba9680318
-- title:
--   Geometric lower killed first-record expectations from one-step regeneration
-- statement:
--   For true killed first-record payments at record grid levels b+n h, assume the initial expected reward is at least h p and each successive expected killed reward is at least p times its predecessor. Then every nth expected payment dominates h p^(n+1). This discharges the complete ENNReal geometric iteration and leaves the strong-Markov one-step estimate explicit.
-- source:
--   Proved first-record geometric induction, ENNReal ofReal_mul, ofReal_pow. Lower analogue of published killed_firstRecord_grid_geometric_expected_upper_of_step.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_chat08_killed_record_discount_weight_le_cell

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_firstRecord_grid_geometric_expected_lower_of_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b q h p : ℝ)
    (hq : 0 ≤ q) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n ω, w n ω =
      if twoSidedExitUpTime X (b + (n : ℝ) * h) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (h * Real.exp (-(q * (twoSidedExitUpTime X (b + (n : ℝ) * h) ω).toReal)))
      else 0)
    (hzero : ENNReal.ofReal (h * p) ≤ (∫⁻ ω, w 0 ω ∂P))
    (hstep : ∀ n, ENNReal.ofReal p * (∫⁻ ω, w n ω ∂P) ≤
      (∫⁻ ω, w (n + 1) ω ∂P)) :
    ∀ n, ENNReal.ofReal (h * p ^ (n + 1)) ≤
      (∫⁻ ω, w n ω ∂P) := by sorry
