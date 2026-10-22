-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_exact_uniform_grid_discount_expectation_tendsto
-- name    : AvramDividend.Classical.chat03_exact_uniform_grid_discount_expectation_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:07:18.437994+00:00
-- url     : https://prove2.me/theorems/e1b0e908-abaf-4e41-9dec-5fca50f49c07
-- title:
--   Exact upper-first uniform-grid discount expectations converge to continuous strict two-sided exit expectation
-- statement:
--   On a probability space, the exact discounted upper-first reward associated with uniform-grid strict upper and lower clocks converges in ENNReal expectation to the official continuous strict upper-before-lower exit discount for any nonnegative discount rate. The accepted exact grid clock measurability theorem supplies each integrand's measurability, the exact pathwise convergence theorem supplies pointwise convergence for every sample path, and the accepted upper-first dominated-convergence theorem transfers the limit through the probability integral. The result is independent of the still unresolved killed-scale martingale identity.
-- source:
--   Accepted Chat 03 dominated-convergence theorem, exact grid clock measurability and exact pathwise payoff convergence.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_uniform_grid_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_exact_uniform_grid_upperfirst_payoff_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_lintegral_tendsto_of_ae_payoff

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_exact_uniform_grid_discount_expectation_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) (hsep : lower < upper)
    (q : ℝ) (hq : 0 ≤ q) (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto
      (fun n => ∫⁻ ω,
        let up := ⨅ k : ℕ,
          if upper < X.X ((k : ℝ≥0) * mesh n) ω then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        let down := ⨅ k : ℕ,
          if X.X ((k : ℝ≥0) * mesh n) ω < lower then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        if up < down then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal up)))
        else 0 ∂P)
      atTop (𝓝 (∫⁻ ω,
        if twoSidedExitUpTime X upper ω <
            twoSidedExitDownTime X lower ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (twoSidedExitUpTime X upper ω))))
        else 0 ∂P)) := by sorry
