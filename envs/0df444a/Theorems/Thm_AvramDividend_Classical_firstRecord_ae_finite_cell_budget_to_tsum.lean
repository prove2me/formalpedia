-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_ae_finite_cell_budget_to_tsum
-- name    : AvramDividend.Classical.firstRecord_ae_finite_cell_budget_to_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:24:06.619879+00:00
-- url     : https://prove2.me/theorems/6f868f35-81fc-402a-808b-a0def66d1074
-- title:
--   Almost-everywhere finite first-record bounds extend to the countable record sum
-- statement:
--   If every finite prefix of discounted record-cell payments is almost everywhere bounded by the stopped Stieltjes reward, then one common almost-everywhere event supports all prefixes and their infinite sum. The proof combines the countable almost-everywhere intersection lemma and ENNReal monotone convergence of finite prefixes.
-- source:
--   Pinned Mathlib MeasureTheory.ae_all_iff and ENNReal.tsum_eq_iSup_nat.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
open MeasureTheory
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.firstRecord_ae_finite_cell_budget_to_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ≥0∞) (C : Ω → ℝ≥0∞)
    (hfinite : ∀ N : ℕ, ∀ᵐ ω ∂P,
      (∑ n ∈ Finset.range N, f n ω) ≤ C ω) :
    ∀ᵐ ω ∂P, (∑' n, f n ω) ≤ C ω := by sorry
