-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenGirth_lemma_27
-- name    : EvenCycleTuran.EvenGirth.lemma_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:15.86304+00:00
-- url     : https://prove2.me/theorems/45f60f55-413f-4c0f-b48e-92d908ed21e4
-- title:
--   Lemma 27, p. 19 — a partition with no P₃ inside V_i (i < s), no P_{p+1} across parts and V_s independent forces |E(G)| ≤ p·n
-- statement:
--   Let $p$ and $s$ be positive integers and let $G$ be a graph on $n$ vertices. Suppose $V(G)$ is partitioned into sets $V_1,\dots,V_s$ (some possibly empty) such that
--
--   1. for $i<s$ there is no path $P_3$ (two edges) with both endpoints in $V_i$;
--   2. there is no path $P_{p+1}$ ($p$ edges) whose two endpoints lie in different parts $V_i\ne V_j$;
--   3. $V_s$ is an independent set.
--
--   Then
--   $$|E(G)|\le p\,n .$$
--
--   The paper states the conclusion as $|E(G)|=O(n)$ for fixed $p$ and $s$; the bound $p\,n$, which does not depend on $s$, is what its proof gives, and it is the form used in Claim 15, where $s-1$ is the degree of a vertex.
--
--   **Formalization Note.** The paper calls this parameter $m$; it is renamed $p$ because $m$ is the parameter of Theorem 14. The partition is a map `part : V → Fin s`; $V_s$ is the fibre of the last index $s-1$. Condition 1 says: no distinct $u,w$ in the same part other than the last with a common neighbour. Condition 2 says: every injective sequence $q_0,\dots,q_p$ of consecutively adjacent vertices has $q_0,q_p$ in the same part.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 19, Lemma 27 and its proof ("G has at most mn = O(n) edges")

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenGirth_Setting
open SimpleGraph Finset Filter Asymptotics

namespace EvenCycleTuran.EvenGirth

/-- Lemma 27 with the explicit bound `|E(G)| ≤ p n` of its proof. The lemma's `m` is renamed
`p` here (it clashes with the `m` of Theorem 14); the parts are `V₁, …, V_s` = the fibres of
`part : V → Fin s`, with `V_s` the fibre of the last index `s - 1`. -/
theorem lemma_27 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (p s : ℕ) (hp : 0 < p) (hs : 0 < s) (part : V → Fin s)
    (h_i : ∀ u w x : V, u ≠ w → part u = part w → (part u).val ≠ s - 1 →
      G.Adj u x → G.Adj x w → False)
    (h_ii : ∀ q : Fin (p + 1) → V, Function.Injective q →
      (∀ i : Fin p, G.Adj (q i.castSucc) (q i.succ)) → part (q 0) = part (q (Fin.last p)))
    (h_iii : ∀ u w : V, (part u).val = s - 1 → (part w).val = s - 1 → ¬ G.Adj u w) :
    #G.edgeFinset ≤ p * Fintype.card V := by sorry

end EvenCycleTuran.EvenGirth
