-- Prove2me | Theorems.Thm_ConsistentSubmodular_SetOperationPath_exists_chain
-- name    : ConsistentSubmodular.SetOperationPath.exists_chain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:15.030663+00:00
-- url     : https://prove2.me/theorems/1199d282-c392-456e-831e-e47a41d6088c
-- title:
--   Concatenating deletion-first changes along a finite sequence of sets
-- statement:
--   Let $S_0,S_1,\dots$ be finite subsets of $[n]$, let $m,B\in\mathbb N$, let $U\subseteq[n]$, and let $\mathrm{good}$ be a property of sets that is upward closed ($A\subseteq A'$ and $\mathrm{good}(A)$ imply $\mathrm{good}(A')$). Assume
--
--   1. $\mathrm{good}(S_0)$;
--   2. for every $i\le m$: $S_i\subseteq U$ and $|S_i|\le B$;
--   3. for every $i<m$: $\mathrm{good}(S_i\cap S_{i+1})$.
--
--   Then there is an operation path $P$ with
--
--   $$P.\mathrm{length}=\sum_{i=0}^{m-1}\operatorname{rec}(S_i,S_{i+1}),\qquad P_0=S_0,\qquad P_{P.\mathrm{length}}=S_m,$$
--
--   such that every node satisfies $P_j\subseteq U$, $|P_j|\le B$ and $\mathrm{good}(P_j)$ (for all $j\in\mathbb N$). Here $\operatorname{rec}(A,A')=|A\triangle A'|$.
--
--   The path is obtained by concatenating the deletion-first realizations of consecutive changes; the property $\mathrm{good}$ (for instance, a lower bound on the objective after adding a fixed buffer) is protected at every intermediate step because every intermediate set contains the intersection of the two endpoints. It is used to turn a sampled sequence of sets into an exact single-element schedule.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/PhysicalOperationPath.lean#L125-L156 (`ConsistentSubmodular.SetOperationPath.exists_chain`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_OperationPath

open ConsistentSubmodular
variable {n : ℕ}
open ConsistentSubmodular.SetOperationPath
open scoped BigOperators

theorem ConsistentSubmodular.SetOperationPath.exists_chain (S : ℕ → Finset (Fin n)) (m B : ℕ) (U : Finset (Fin n))
    (good : Finset (Fin n) → Prop)
    (hmono : ∀ A B, A ⊆ B → good A → good B)
    (hstart : good (S 0))
    (hnodes : ∀ i, i ≤ m → S i ⊆ U ∧ (S i).card ≤ B)
    (hinter : ∀ i, i < m → good (S i ∩ S (i + 1))) :
    ∃ P : SetOperationPath n,
      P.length = ∑ i ∈ Finset.range m, recourse (S i) (S (i + 1)) ∧
      P.node 0 = S 0 ∧ P.node P.length = S m ∧
      ∀ i, P.node i ⊆ U ∧ (P.node i).card ≤ B ∧ good (P.node i) := by sorry
