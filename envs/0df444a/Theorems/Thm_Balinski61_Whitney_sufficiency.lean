-- Prove2me | Theorems.Thm_Balinski61_Whitney_sufficiency
-- name    : Balinski61.Whitney.sufficiency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T16:04:49.069293+00:00
-- url     : https://prove2.me/theorems/ad5b45a8-e56c-4bc8-9211-01b9d7346494
-- title:
--   p. 434, proof of WHITNEY'S THEOREM — n disjoint paths between all pairs imply n-tuple connectedness
-- statement:
--   Let $G$ be a finite graph with at least two points, and suppose that for every pair of distinct points $p_s, p_k$ there are $n$ disjoint paths from $p_s$ to $p_k$. Then $G$ is $n$-tuply connected:
--   $$
--   |V| \ge n+1 \quad\text{and}\quad G - X \text{ is connected whenever } |X| < n .
--   $$
--
--   This is the "if" half of Whitney's theorem, which the paper calls obvious.
--
--   **Formalization Note** The hypothesis of at least two points is added: on a graph with one point (or none) the path condition holds vacuously, but the graph is not $n$-tuply connected for $n \ge 1$ (respectively for any $n$). The paper takes the existence of a pair of points for granted.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 434, proof of WHITNEY'S THEOREM (sufficiency)

import Mathlib
import Definitions.Def_Balinski61_Whitney_Graph

namespace Balinski61.Whitney

theorem sufficiency {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ)
    (hcard : 2 ≤ Fintype.card V)
    (hpaths : ∀ ps pk : V, ps ≠ pk → HasNDisjointPaths G n ps pk) :
    IsNTuplyConnected G n := by sorry

end Balinski61.Whitney
