-- Prove2me | Theorems.Thm_CircStability_Bondy_theorem_1_12
-- name    : CircStability.Bondy.theorem_1_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:35.981794+00:00
-- url     : https://prove2.me/theorems/df9a1fa1-a0fb-4072-ac51-f60fc7e2e342
-- title:
--   Theorem 1.12 — a 2-connected graph with more than (⌊c/2⌋−1)(n−c) edges off a longest cycle of length 10 ≤ c < n lies in W_{n,⌊c/2⌋,c} or (c odd) in X_{n,c} ∪ Y_{n,c}
-- statement:
--   Let $G$ be a 2-connected graph on $n$ vertices and let $C$ be a longest cycle of $G$ of length $c$, where $10 \le c \le n-1$. Suppose the number of edges of $G$ with at most one endpoint in $C$ is more than $(\lfloor c/2\rfloor - 1)(n-c)$, that is,
--
--   $$e(G-C) + e(G-C,C) > \left(\left\lfloor \tfrac c2\right\rfloor - 1\right)(n-c).$$
--
--   Then either
--
--   1. $G \subseteq W_{n,\lfloor c/2\rfloor,c}$, i.e. $G$ is isomorphic to a subgraph of $W_{n,\lfloor c/2\rfloor,c}$; or
--   2. $c$ is odd and $G$ is a subgraph of a member of $\mathcal X_{n,c}\cup\mathcal Y_{n,c}$.
--
--   This is a stability version of Bondy's circumference theorem: a 2-connected graph with this many edges off a longest cycle is a subgraph of one of the extremal graphs. It is one of the two halves of the paper's proof of its main stability theorem for graphs of given circumference and minimum degree.
--
--   **Formalization Note** The edge count is taken with respect to the fixed longest cycle $C$. "$G \subseteq W$" is a graph embedding (`⊑`), never containment on fixed labels; the second alternative is the conjunction "$c$ is odd and …". With $10 \le c \le n-1$ the natural-number expression $(\lfloor c/2\rfloor - 1)(n-c)$ is exact.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 5, Theorem 1.12 (restated on p. 11)

import Mathlib
import Definitions.Def_CircStability_Bondy_Setting
open SimpleGraph Finset

namespace CircStability.Bondy
theorem theorem_1_12 (n c : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : TwoConnected G) {u : Fin n} (C : G.Walk u u) (hC : IsLongestCycle G C)
    (hlen : C.length = c) (hc : 10 ≤ c) (hcn : c < n)
    (hE : (c / 2 - 1) * (n - c) < edgesOffCycle G (cycleVerts C)) :
    G ⊑ wGraph n (c / 2) c ∨
      (Odd c ∧ ∃ H : SimpleGraph (Fin n), (IsXMember n c H ∨ IsYMember n c H) ∧ G ≤ H) := by sorry
end CircStability.Bondy
