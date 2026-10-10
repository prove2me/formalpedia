-- Prove2me | Theorems.Thm_CircStability_Bondy_lemma_3_3
-- name    : CircStability.Bondy.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:25.793076+00:00
-- url     : https://prove2.me/theorems/421594ec-0dcc-4f63-8e40-bbed6faf63bb
-- title:
--   Lemma 3.3 — an isolated vertex of G − C with ⌊c/2⌋ neighbours on C forces G ⊆ W_{n,⌊c/2⌋,c} (c even), or G ⊆ W or ⊆ a member of X ∪ Y (c ≥ 9 odd)
-- statement:
--   Let $G$ be a 2-connected non-Hamiltonian graph on $n$ vertices and let $C$ be a longest cycle of $G$ of length $c$. Suppose there is an isolated vertex $u$ of $G - C$ (so $u \notin V(C)$ and all neighbours of $u$ lie on $C$) with $d_C(u) = \lfloor c/2\rfloor$. Then:
--
--   1. if $c$ is even, $G \subseteq W_{n,\lfloor c/2\rfloor,c}$;
--   2. if $c \ge 9$ is odd, then $G \subseteq W_{n,\lfloor c/2\rfloor,c}$ or $G$ is a subgraph of a member of $\mathcal X_{n,c} \cup \mathcal Y_{n,c}$.
--
--   Here $G \subseteq W$ means that $G$ is isomorphic to a subgraph of $W$. The lemma converts the vertex produced by Theorem 3.1 into the structure asserted by the stability theorem.
--
--   **Formalization Note** Non-Hamiltonicity is Mathlib's `IsHamiltonian`, which for $n \ne 1$ means having a Hamiltonian cycle; the hypothesis is kept as on the page although it follows from the others. Containment in $W_{n,\lfloor c/2\rfloor,c}$ is a graph embedding (`⊑`); containment in a member of $\mathcal X_{n,c} \cup \mathcal Y_{n,c}$ is `G ≤ H` for a labelled member $H$.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 15, Lemma 3.3

import Mathlib
import Definitions.Def_CircStability_Bondy_Setting
open SimpleGraph Finset

namespace CircStability.Bondy
theorem lemma_3_3 (n c : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : TwoConnected G) (hNH : ¬ G.IsHamiltonian) {u : Fin n} (C : G.Walk u u)
    (hC : IsLongestCycle G C) (hlen : C.length = c)
    (v : Fin n) (hv : v ∉ cycleVerts C) (hviso : ∀ w, G.Adj v w → w ∈ cycleVerts C)
    (hdeg : #(G.neighborFinset v ∩ cycleVerts C) = c / 2) :
    (Even c → G ⊑ wGraph n (c / 2) c) ∧
      (9 ≤ c → Odd c → G ⊑ wGraph n (c / 2) c ∨
        ∃ H : SimpleGraph (Fin n), (IsXMember n c H ∨ IsYMember n c H) ∧ G ≤ H) := by sorry
end CircStability.Bondy
