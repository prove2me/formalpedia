-- Prove2me | Theorems.Thm_CircStability_Main_theorem_1_12
-- name    : CircStability.Main.theorem_1_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:20.36074+00:00
-- url     : https://prove2.me/theorems/1f70843c-0f14-401d-bf9e-92ef0afe258e
-- title:
--   Theorem 1.12 — more than (⌊c/2⌋−1)(n−c) edges off a longest cycle of length 10 ≤ c ≤ n−1 give G ⊆ W_{n,⌊c/2⌋,c} or (c odd) G in X_{n,c} ∪ Y_{n,c}
-- statement:
--   Let $G$ be a 2-connected graph on $n$ vertices and $C$ a longest cycle of $G$ of length $c$, where $10\le c\le n-1$. If the number of edges with at most one endpoint in $C$ is more than
--
--   $$
--   \big(\lfloor c/2\rfloor-1\big)(n-c),
--   $$
--
--   then either $G\subseteq W_{n,\lfloor c/2\rfloor,c}$, or $c$ is odd and $G$ is a subgraph of a member of $\mathcal X_{n,c}\cup\mathcal Y_{n,c}$.
--
--   This is the paper's stability version of Bondy's theorem, and the first branch of the proof of Theorem 1.9. It is the goal of the companion mission; it is restated here so that this mission's attack path is complete.
--
--   **Formalization Note.** "$G\subseteq W$" is an embedding of $G$ into $W$ (Mathlib's `⊑`). "A subgraph of a member" is $G\le H$ for some $H$ on the same vertex set lying in the family; both families are closed under relabelling. "$c$ is odd and …" is a conjunction inside the disjunction.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 5, Theorem 1.12 (restated p. 11)

import Mathlib
import Definitions.Def_CircStability_Main_Setting
open Finset SimpleGraph

namespace CircStability.Main

theorem theorem_1_12 (n c : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : TwoConnected G)
    {u : Fin n} (C : G.Walk u u) (hC : IsLongestCycle G C) (hlen : C.length = c)
    (hc : 10 ≤ c) (hcn : c ≤ n - 1)
    (hE : (c / 2 - 1) * (n - c) < edgesOffCycle G C.support.toFinset) :
    G ⊑ wGraph n (c / 2) c ∨
      (Odd c ∧ ∃ H : SimpleGraph (Fin n), (IsXMember n c H ∨ IsYMember n c H) ∧ G ≤ H) := by sorry

end CircStability.Main
