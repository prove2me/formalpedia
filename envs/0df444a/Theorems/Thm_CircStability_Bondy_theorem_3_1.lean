-- Prove2me | Theorems.Thm_CircStability_Bondy_theorem_3_1
-- name    : CircStability.Bondy.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:40.161581+00:00
-- url     : https://prove2.me/theorems/14fc3cbd-1cf8-4df4-b3dd-d6046e468f83
-- title:
--   Theorem 3.1 — many edges off a longest cycle of length 10 ≤ c < n give an isolated vertex of G − C with ⌊c/2⌋ neighbours on C
-- statement:
--   Let $G$ be a 2-connected graph on $n$ vertices and let $C$ be a longest cycle of $G$ of length $c$, where $10 \le c \le n-1$. If
--
--   $$e(G-C) + e(G-C, C) > \left(\left\lfloor \tfrac c2 \right\rfloor - 1\right)(n-c),$$
--
--   then there is an isolated vertex $u$ of $G - C$ (that is, $u \notin V(C)$ and all neighbours of $u$ lie on $C$) with exactly $d_C(u) = \lfloor c/2\rfloor$ neighbours on $C$.
--
--   The existence of such a vertex is what yields the structural description of $G$ in the stability theorem.
--
--   **Formalization Note** $e(G-C)+e(G-C,C)$ is the number of edges with at most one endpoint in $V(C)$.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 11, Theorem 3.1

import Mathlib
import Definitions.Def_CircStability_Bondy_Setting
open SimpleGraph Finset

namespace CircStability.Bondy
theorem theorem_3_1 (n c : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : TwoConnected G) {u : Fin n} (C : G.Walk u u) (hC : IsLongestCycle G C)
    (hlen : C.length = c) (hc : 10 ≤ c) (hcn : c < n)
    (hE : (c / 2 - 1) * (n - c) < edgesOffCycle G (cycleVerts C)) :
    ∃ v, v ∉ cycleVerts C ∧ (∀ w, G.Adj v w → w ∈ cycleVerts C) ∧
      #(G.neighborFinset v ∩ cycleVerts C) = c / 2 := by sorry
end CircStability.Bondy
