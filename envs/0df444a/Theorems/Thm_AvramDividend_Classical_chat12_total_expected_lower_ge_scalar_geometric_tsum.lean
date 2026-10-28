-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_total_expected_lower_ge_scalar_geometric_tsum
-- name    : AvramDividend.Classical.chat12_total_expected_lower_ge_scalar_geometric_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:37:13.922993+00:00
-- url     : https://prove2.me/theorems/e7cc7c0b-7f23-44e1-93ba-3c38e362619f
-- title:
--   Total expected surviving killed-record payments dominate lower geometric series
-- statement:
--   Suppose the strict discounted ε-up-before-(ε-a)-down exit expectation is ENNReal.ofReal p with p≥0. Then the sum over record levels n≥1 of their expected discounted killed rewards dominates the extended-real geometric series Σ ENNReal.ofReal (epsilon*p^(n+1)). The proof sums the Proved unconditional scale-free geometric lower record expectation termwise and converts nonnegative real products and powers to ENNReal. It is independent of the Open q-scale-function exit ratio and Chat 5's pathwise dividend-measure budget.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_chat12_firstRecord_geometric_trueExit_lower

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_total_expected_lower_ge_scalar_geometric_tsum
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
    (∑' n : ℕ, ENNReal.ofReal (ε * p ^ (n + 1))) ≤
      (∑' n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) := by sorry
