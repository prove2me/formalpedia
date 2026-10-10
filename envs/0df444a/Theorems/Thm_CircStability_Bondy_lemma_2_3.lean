-- Prove2me | Theorems.Thm_CircStability_Bondy_lemma_2_3
-- name    : CircStability.Bondy.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:07.129988+00:00
-- url     : https://prove2.me/theorems/a3996cd7-d1c9-4498-bb52-4499b2abc711
-- title:
--   Lemma 2.3 — a 2-connected component H of G − C has average G-degree r ≤ c/2, with equality only if H is a clique with two common neighbours on C
-- statement:
--   Let $G$ be a 2-connected graph, let $C$ be a longest cycle of $G$ of length $c$, and let $H$ be a component of $G - C$ which is 2-connected. Let $r$ be the average degree in $G$ of the vertices of $H$. Then
--
--   $$c \ge 2r, \qquad\text{i.e.}\qquad 2\sum_{v \in V(H)} d_G(v) \le c\,|V(H)|,$$
--
--   and if equality holds, then $H$ is a clique (necessarily $K_{r-1}$) in which every vertex has the same two neighbours on $C$: there are distinct $a,b \in V(C)$ with $N_G(v) \cap V(C) = \{a,b\}$ for all $v \in V(H)$.
--
--   The lemma bounds how dense a 2-connected piece outside a longest cycle can be, and identifies the extremal configuration.
--
--   **Formalization Note** $H$ is given by its vertex set; it is a component of $G - V(C)$ and its induced subgraph is 2-connected. That $H$ has exactly $r-1$ vertices follows from the stated conclusion (each vertex then has degree $(|H|-1)+2$), so it is not stated separately.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 7, Lemma 2.3 (Theorem 2 of [9])

import Mathlib
import Definitions.Def_CircStability_Bondy_Setting
open SimpleGraph Finset

namespace CircStability.Bondy
theorem lemma_2_3 (n c : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : TwoConnected G) {u : Fin n} (C : G.Walk u u) (hC : IsLongestCycle G C)
    (hlen : C.length = c) (H : Finset (Fin n)) (hH : IsComponentOff G (cycleVerts C) H)
    (hH2 : TwoConnected (G.induce (H : Set (Fin n)))) :
    2 * ∑ v ∈ H, G.degree v ≤ c * #H ∧
      (2 * ∑ v ∈ H, G.degree v = c * #H →
        (∀ v ∈ H, ∀ w ∈ H, v ≠ w → G.Adj v w) ∧
        ∃ a ∈ cycleVerts C, ∃ b ∈ cycleVerts C, a ≠ b ∧
          ∀ v ∈ H, G.neighborFinset v ∩ cycleVerts C = {a, b}) := by sorry
end CircStability.Bondy
