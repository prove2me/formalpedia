-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_lintegral_tendsto_of_ae_payoff
-- name    : AvramDividend.Classical.chat03_grid_upperfirst_lintegral_tendsto_of_ae_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:17:24.721767+00:00
-- url     : https://prove2.me/theorems/0b09622e-3994-481a-9594-e3dbd3d76d29
-- title:
--   Dominated convergence of upper-first grid discount expectations from almost-everywhere payoff convergence
-- statement:
--   For a probability measure, nonnegative discount q and measurable upper and lower grid-passage clocks, if the exact conditional discounted reward converges almost everywhere to its continuous upper-first analogue, then the ENNReal expectations converge. Every approximating payoff is uniformly bounded by one, independently of grid size, by the accepted pointwise upper-first reward bound. The pinned Lebesgue dominated-convergence theorem yields convergence of the expectations without any additional uniform-integrability assumption and with the exact ENNReal.toReal and ofReal conventions. This is the key expectation-limit bridge for Chat 03 finite-grid to continuous stopped-scale passage, separating the pathwise crossing task from the stochastic harmonicity task.
-- source:
--   Pinned Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence and accepted Chat03 upper-first reward bound ca2f713b-22b7-4816-94d2-120e3e3a1147.

import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_upperfirst_weight_le_one

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.chat03_grid_upperfirst_lintegral_tendsto_of_ae_payoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ) (hq : 0 ≤ q)
    (upGrid downGrid : ℕ → Ω → ℝ≥0∞)
    (up down : Ω → ℝ≥0∞)
    (hu : ∀ n, Measurable (upGrid n))
    (hd : ∀ n, Measurable (downGrid n))
    (hlim : ∀ᵐ ω ∂P,
      Tendsto
        (fun n => if upGrid n ω < downGrid n ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (upGrid n ω))))
        else 0) atTop
        (𝓝 (if up ω < down ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (up ω))))
        else 0))) :
    Tendsto
      (fun n => ∫⁻ ω,
        if upGrid n ω < downGrid n ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (upGrid n ω))))
        else 0 ∂P)
      atTop
      (𝓝 (∫⁻ ω,
        if up ω < down ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (up ω))))
        else 0 ∂P)) := by sorry
