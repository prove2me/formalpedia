-- Prove2me | Theorems.Thm_CircStability_Bondy_theorem_2_2
-- name    : CircStability.Bondy.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:30.852416+00:00
-- url     : https://prove2.me/theorems/b53c9878-db5b-431b-b1a9-87bd27534de2
-- title:
--   Theorem 2.2 (Fan), first assertion — in a 2-connected graph a longest (x,y)-path is at least the average degree off x, y
-- statement:
--   Let $x,y$ be two distinct vertices of a 2-connected graph $G$ on $n$ vertices, and let $r$ be the average degree (in $G$) of the $n-2$ vertices other than $x$ and $y$. Then $G$ has an $(x,y)$-path of length at least $r$; equivalently, there is an $(x,y)$-path $P$ with
--
--   $$\sum_{v \ne x,y} d_G(v) \le (n-2)\,|E(P)|.$$
--
--   This average-degree version of the Erdős–Gallai path theorem is due to Fan and is used to find long paths between prescribed vertices.
--
--   **Formalization Note** Only the first assertion of the paper's Theorem 2.2 is stated; the characterization of the equality case ($r$ an integer and $G \in \{J, J-xy\}$) is omitted. The average is cleared of its denominator $n-2 \ge 1$.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 7, Theorem 2.2 (Fan [9]), first assertion

import Mathlib
import Definitions.Def_CircStability_Bondy_Setting
open SimpleGraph Finset

namespace CircStability.Bondy
theorem theorem_2_2 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : TwoConnected G) (x y : Fin n) (hxy : x ≠ y) :
    ∃ p : G.Walk x y, p.IsPath ∧
      ∑ v ∈ univ \ {x, y}, G.degree v ≤ (n - 2) * p.length := by sorry
end CircStability.Bondy
