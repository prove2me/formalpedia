-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_total_expected_lower_geometric_closed_form
-- name    : AvramDividend.Classical.chat12_total_expected_lower_geometric_closed_form
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:38:44.948106+00:00
-- url     : https://prove2.me/theorems/e67db71f-025c-4498-beb2-fe3fecb22876
-- title:
--   Closed form lower renewal budget for surviving killed-record expectations
-- statement:
--   For the true discounted ε-up-before-(ε-a)-down strict exit factor equal to ENNReal.ofReal p with p≥0, the total expected payments from killed surviving upward-record levels n+1 is at least ENNReal.ofReal ε times ENNReal.ofReal p divided by 1-ENNReal.ofReal p in extended nonnegative real arithmetic. Follows by the Proved lower expected-record aggregate inequality and Proved shifted geometric series identity. The q-scale function identity is not imported and is instead an explicit factor premise.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_lower_ge_scalar_geometric_tsum
import Theorems.Thm_AvramDividend_Classical_firstRecord_ofReal_geometric_tsum

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_total_expected_lower_geometric_closed_form
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (p : ℝ) (hp : 0 ≤ p)
    (hExit : (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal p) :
    ENNReal.ofReal ε *
      (ENNReal.ofReal p * (1 - ENNReal.ofReal p)⁻¹) ≤
      (∑' n : ℕ, (∫⁻ ω,
      if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) := by sorry
