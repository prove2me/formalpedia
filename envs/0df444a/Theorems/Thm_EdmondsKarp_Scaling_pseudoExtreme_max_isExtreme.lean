-- Prove2me | Theorems.Thm_EdmondsKarp_Scaling_pseudoExtreme_max_isExtreme
-- name    : EdmondsKarp.Scaling.pseudoExtreme_max_isExtreme
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:25:37.000652+00:00
-- url     : https://prove2.me/theorems/0958ea2f-5a04-4398-8e12-f1f87acc88f2
-- title:
--   §2.2 — a pseudo-extreme maximum flow of the Hitchcock problem is extreme
-- statement:
--   Consider the Hitchcock network of Figure 1 with $m, n \ge 1$, positive capacities $a_i$, $b_j$ with $\sum_i a_i = \sum_j b_j$, and nonnegative costs $d_{ij}$. If $f$ is a maximum flow and $f$ is pseudo-extreme, that is, there are real $u_i$, $v_j$ with
--   $$u_i - v_j + d_{ij} \ge 0 \quad\text{and}\quad u_i - v_j + d_{ij} > 0 \Rightarrow f_{ij} = 0$$
--   for all $i, j$, then $f$ is extreme.
--
--   This is the fact on which the scaling method rests: it only has to maintain the two conditions (5a)–(5b), and the maximum flow it ends with in Problem $0$ is then of minimum cost. The balance $\sum a_i = \sum b_j$ is needed; for unbalanced problems the implication fails in general.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 259, §2.2 (unnumbered: 'A pseudo-extreme maximum flow is extreme')

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport

namespace EdmondsKarp.Scaling

/-- §2.2, p. 259 (unnumbered): for the Hitchcock problem (`∑ a_i = ∑ b_j`), a pseudo-extreme maximum
flow is extreme. -/
theorem pseudoExtreme_max_isExtreme {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (T : Transport m n)
    (ha : ∀ i, 0 < T.a i) (hb : ∀ j, 0 < T.b j) (hsum : ∑ i, T.a i = ∑ j, T.b j)
    (hd : ∀ i j, 0 ≤ T.d i j) (x : Flow m n) (hmax : IsMaxFlow T x)
    (hpe : IsPseudoExtreme T x) :
    IsExtreme T x := by sorry

end EdmondsKarp.Scaling
