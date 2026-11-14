-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_exists_insertion_first_bridge
-- name    : ConsistentSubmodular.Objective.exists_insertion_first_bridge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:02.943304+00:00
-- url     : https://prove2.me/theorems/e2cca12c-7957-4363-8874-6b43f48e9526
-- title:
--   Insertion-first bridge between two sets of value at least $V$ after a buffer
-- statement:
--   Let $f$ be a nonnegative monotone submodular function on subsets of $[n]$, let $A,B,Q\subseteq[n]$ and $V\in\mathbb R$ with
--
--   $$V\le f(Q\cup A),\qquad V\le f(Q\cup B).$$
--
--   Then there is an operation path $P$ (consecutive sets differ by at most one element) with $P_0=A$, $P_{P.\mathrm{length}}=B$, $P.\mathrm{length}\le |A|+|B|$, and for every node $P_j$:
--
--   $$P_j\subseteq A\cup B,\qquad |P_j|\le |A|+|B|,\qquad V\le f(Q\cup P_j).$$
--
--   The path first inserts the elements of $B\setminus A$ and then deletes those of $A\setminus B$, so the value after adding the buffer $Q$ never drops below $V$ (by monotonicity, every node contains $A$ or $B$). It is the exact (unrounded) bridge between two endpoints of equal scale, used when the sets are small compared with the rounding overhead.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/BridgeSmall.lean#L12-L33 (`ConsistentSubmodular.Objective.exists_insertion_first_bridge`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_OperationPath

open ConsistentSubmodular
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.exists_insertion_first_bridge (A B Q : Finset (Fin n)) (V : ℝ)
    (hA : V ≤ f.value (Q ∪ A)) (hB : V ≤ f.value (Q ∪ B)) :
    ∃ P : SetOperationPath n, P.node 0 = A ∧ P.node P.length = B ∧
      P.length ≤ A.card + B.card ∧ ∀ j, P.node j ⊆ A ∪ B ∧
        (P.node j).card ≤ A.card + B.card ∧ V ≤ f.value (Q ∪ P.node j) := by sorry
