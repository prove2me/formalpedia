-- Prove2me | Theorems.Thm_ConsiderChoose_StateSpace_lemma_2
-- name    : ConsiderChoose.StateSpace.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:56.259963+00:00
-- url     : https://prove2.me/theorems/ed0dd55c-0993-4d5e-8752-4035b4c56f80
-- title:
--   Lemma 2 (Central Lemma), p. 15 — Φ is injective on the state space, so |𝒮| = |Φ⟨𝒮⟩|
-- statement:
--   Let $C_1,\dots,C_K\subseteq[N]$ be consideration sets over products numbered in the common preference order, let $\mathcal S$ be the state space of the dynamic program of §3 (the distinct nontrivial connected subproblems $(S,T)$ generated from the components of $G[[N],[K]]$ by stocking or skipping $\min(S)$), and let
--   $$\Phi(S,T)=[\min(S)]\cap\bigcup_{u\in T}C_u\subseteq[N].$$
--   Then $\Phi$ is injective on $\mathcal S$, and consequently
--   $$|\mathcal S|=|\Phi\langle\mathcal S\rangle|.$$
--
--   The lemma turns counting the states of the dynamic program into counting subsets of products, which is how Theorem 1 and the paper's later running-time bounds for structured consideration sets are obtained.
--
--   **Formalization Note.** $\mathcal S$ is the inductively generated `stateSpace C`; trivial components (no product or no type) are not states. The second conjunct is the cardinality identity $|\Phi\langle\mathcal S\rangle|=|\mathcal S|$ with `Set.ncard` on finite sets.
-- source:
--   Aouad, Farias & Levi (2021), Management Science 67(6), accepted manuscript (LBS eprint 1426), p. 15, Lemma 2 (Central Lemma)

import Mathlib
import Definitions.Def_ConsiderChoose_StateSpace_Model

namespace ConsiderChoose.StateSpace

theorem lemma_2 {N K : ℕ} (C : Fin K → Finset (Fin N)) :
    Set.InjOn (fun p : Finset (Fin N) × Finset (Fin K) => Phi C p.1 p.2) (stateSpace C) ∧
      ((fun p : Finset (Fin N) × Finset (Fin K) => Phi C p.1 p.2) '' stateSpace C).ncard =
        (stateSpace C).ncard := by sorry

end ConsiderChoose.StateSpace
