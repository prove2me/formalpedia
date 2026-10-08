-- Prove2me | Theorems.Thm_FiniteSortedRealCutListCoversUnitInterval
-- name    : FiniteSortedRealCutListCoversUnitInterval
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:26:15.02674+00:00
-- url     : https://prove2.me/theorems/f2c50331-52e3-4010-b404-380181692088
-- title:
--   Finite Sorted Real Cut List Covers Unit Interval
-- statement:
--   Let $L$ be a strictly increasing finite list of real numbers.  Suppose
--   $0\in L$, $1\in L$, and every entry of $L$ lies in the interval
--   $[0,1]$.  Then every $t\in[0,1]$ lies in one of the closed consecutive
--   gaps $[L_k,L_{k+1}]$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `FiniteSortedRealCutListCoversUnitInterval`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FiniteSortedRealCutListCoversUnitInterval.lean#L1-L67

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic

open Classical
noncomputable section

lemma FiniteSortedRealCutListCoversUnitInterval
    (L : List ℝ)
    (hSorted : L.SortedLT)
    (hzero : (0 : ℝ) ∈ L) (hone : (1 : ℝ) ∈ L)
    (hbounds : ∀ t : ℝ, t ∈ L → 0 ≤ t ∧ t ≤ 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ k, ∃ hk : k + 1 < L.length,
      t ∈ segment ℝ (L[k]'(Nat.lt_of_succ_lt hk)) (L[k + 1]'hk) := by sorry
