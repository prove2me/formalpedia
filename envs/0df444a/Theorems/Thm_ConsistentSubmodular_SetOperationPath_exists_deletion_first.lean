-- Prove2me | Theorems.Thm_ConsistentSubmodular_SetOperationPath_exists_deletion_first
-- name    : ConsistentSubmodular.SetOperationPath.exists_deletion_first
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:14.596429+00:00
-- url     : https://prove2.me/theorems/3e73a132-7169-419e-97c1-e82a4c4cd10b
-- title:
--   Deletion-first realization of a change of physical sets
-- statement:
--   Let $A,B\subseteq[n]$ be finite sets and write $\operatorname{rec}(A,B)=|A\,\triangle\,B|$ for their symmetric difference. Then there is an operation path $P$ (a sequence of sets in which consecutive sets differ by at most one insertion or deletion, constant after its length $\ell=P.\mathrm{length}$) such that
--
--   $$\ell=\operatorname{rec}(A,B),\qquad P_0=A,\qquad P_\ell=B,$$
--
--   and for every index $i\in\mathbb N$,
--
--   $$A\cap B\subseteq P_i\subseteq A\cup B,\qquad |P_i|\le\max\{|A|,|B|\}.$$
--
--   So the change $A\to B$ can be carried out using exactly $|A\triangle B|$ elementary operations (all deletions of $A\setminus B$ first, then the insertions of $B\setminus A$), never touching $A\cap B$ and never using more space than the larger endpoint.
--
--   This is the basic bookkeeping step that converts a change between two physical sets into a sequence of single-element updates, so that the consistency budget is charged exactly the symmetric difference.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/PhysicalOperationPath.lean#L82-L117 (`ConsistentSubmodular.SetOperationPath.exists_deletion_first`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_OperationPath

open ConsistentSubmodular
variable {n : ℕ}
open ConsistentSubmodular.SetOperationPath

theorem ConsistentSubmodular.SetOperationPath.exists_deletion_first (A B : Finset (Fin n)) :
    ∃ P : SetOperationPath n, P.length = recourse A B ∧ P.node 0 = A ∧
      P.node P.length = B ∧ ∀ i,
        A ∩ B ⊆ P.node i ∧ P.node i ⊆ A ∪ B ∧
          (P.node i).card ≤ max A.card B.card := by sorry
