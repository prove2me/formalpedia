-- Prove2me | Theorems.Thm_ConsistentSubmodular_SetOperationPath_exists_chain_fin
-- name    : ConsistentSubmodular.SetOperationPath.exists_chain_fin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:26.493487+00:00
-- url     : https://prove2.me/theorems/d0e6dac5-d622-407d-be0f-3c58d4d39cab
-- title:
--   Deletion-first realization of a $\mathrm{Fin}$-indexed sampling sequence
-- statement:
--   Let $K,B\in\mathbb N$, let $S_0,\dots,S_K$ be finite subsets of $[n]$, let $U\subseteq[n]$, and let $\mathrm{good}$ be an upward-closed property of sets. Assume
--
--   1. $\mathrm{good}(S_0)$;
--   2. $S_i\subseteq U$ and $|S_i|\le B$ for every $i\in\{0,\dots,K\}$;
--   3. $\mathrm{good}(S_i\cap S_{i+1})$ for every $i<K$.
--
--   Then there is an operation path $P$ with
--
--   $$P.\mathrm{length}=\sum_{i<K}|S_i\triangle S_{i+1}|,\qquad P_0=S_0,\qquad P_{P.\mathrm{length}}=S_K,$$
--
--   and $P_j\subseteq U$, $|P_j|\le B$, $\mathrm{good}(P_j)$ for every $j\in\mathbb N$.
--
--   This is the same statement as the chain lemma for $\mathbb N$-indexed sequences, in the form that directly matches the output of simultaneous threshold rounding.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ForcedPath.lean#L58-L86 (`ConsistentSubmodular.SetOperationPath.exists_chain_fin`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_OperationPath

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.SetOperationPath
variable {n : ℕ}

theorem ConsistentSubmodular.SetOperationPath.exists_chain_fin {K : ℕ} (S : Fin (K + 1) → Finset (Fin n))
    (B : ℕ) (U : Finset (Fin n)) (good : Finset (Fin n) → Prop)
    (hmono : ∀ A B, A ⊆ B → good A → good B)
    (hstart : good (S 0))
    (hnodes : ∀ i, S i ⊆ U ∧ (S i).card ≤ B)
    (hinter : ∀ i : Fin K, good (S i.castSucc ∩ S i.succ)) :
    ∃ P : SetOperationPath n,
      P.length = ∑ i : Fin K, recourse (S i.castSucc) (S i.succ) ∧
      P.node 0 = S 0 ∧ P.node P.length = S (Fin.last K) ∧
      ∀ i, P.node i ⊆ U ∧ (P.node i).card ≤ B ∧ good (P.node i) := by sorry
