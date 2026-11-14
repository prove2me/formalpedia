-- Prove2me | Theorems.Thm_ConsistentSubmodular_SetOperationPath_exists_insertion_path
-- name    : ConsistentSubmodular.SetOperationPath.exists_insertion_path
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:19.953294+00:00
-- url     : https://prove2.me/theorems/d8f6e84f-3636-47a5-8009-da3a93417ca8
-- title:
--   Insertion path from $A$ to $A\cup C$ with one element per step
-- statement:
--   For finite sets $A,C\subseteq\{0,\dots,n-1\}$ there exists a set operation path $P$ (a sequence of sets $P_0,P_1,\dots$ that is constant from its length $L$ on and changes by at most one element per step, $|P_{i+1}\triangle P_i|\le 1$) such that
--
--   1. its length is $L=|C|$,
--   2. $P_0=A$ and $P_L=A\cup C$, and
--   3. every node satisfies $A\subseteq P_i\subseteq A\cup C$.
--
--   Thus any finite list of elements can be inserted one at a time, with stuttering steps harmlessly allowed when an inserted element is already present. This is used to realize a change of set as a short sequence of single-element updates.
--
--   **Formalization Note**: the length is exactly $|C|$ and not $|C\setminus A|$; steps for elements already in $A$ leave the set unchanged.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/PhysicalOperationPath.lean#L47-L80 (`ConsistentSubmodular.SetOperationPath.exists_insertion_path`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_OperationPath

open ConsistentSubmodular
variable {n : ℕ}
open ConsistentSubmodular.SetOperationPath

theorem ConsistentSubmodular.SetOperationPath.exists_insertion_path (A C : Finset (Fin n)) :
    ∃ P : SetOperationPath n, P.length = C.card ∧ P.node 0 = A ∧
      P.node P.length = A ∪ C ∧ ∀ i, A ⊆ P.node i ∧ P.node i ⊆ A ∪ C := by sorry
