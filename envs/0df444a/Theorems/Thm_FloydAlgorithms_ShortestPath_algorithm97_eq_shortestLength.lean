-- Prove2me | Theorems.Thm_FloydAlgorithms_ShortestPath_algorithm97_eq_shortestLength
-- name    : FloydAlgorithms.ShortestPath.algorithm97_eq_shortestLength
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:25:52.91159+00:00
-- url     : https://prove2.me/theorems/b6991d9f-3afe-489a-a33f-39aaa0297a19
-- title:
--   Algorithm 97 computes every shortest path length
-- statement:
--   Let $w$ assign a real length to every direct link in a directed network of $n$ points, with $\infty$ where no direct link exists. Assume every closed path in the network has nonnegative length. For all points $i$ and $j$, Floyd's Algorithm 97 leaves in entry $(i,j)$ exactly the shortest path length:
--
--   $$
--   \operatorname{shortestPath}(w)(i,j)=d_w(i,j).
--   $$
--
--   The equality also says that the final entry is $\infty$ when no path exists. It characterizes the complete output matrix, including diagonal entries and negative individual links.
--
--   **Formalization Note** The no-negative-cycle condition is added because the paper omits a necessary premise: on a one-point network with self-link length $-1$, the procedure produces $-2$ instead of the shortest simple closed-path length $-1$. The paper's finite sentinel `₁₀10` is represented as $\infty$, indices are zero-based, and arithmetic is exact real arithmetic. No nonnegativity of individual links or zero diagonal is assumed.
-- source:
--   Floyd, Algorithm 97: Shortest Path, Communications of the ACM 5(6) (1962), p. 345, comment, third and fourth sentences; https://doi.org/10.1145/367766.368168

import Mathlib
import Definitions.Def_FloydAlgorithms_ShortestPath_Network
import Definitions.Def_FloydAlgorithms_ShortestPath_Algorithm97

namespace FloydAlgorithms.ShortestPath

/-- Algorithm 97, comment, third and fourth sentences, p. 345. The
no-negative-cycle condition repairs the paper's unstated necessary premise. -/
theorem algorithm97_eq_shortestLength {n : ℕ} (w : LengthMatrix n)
    (hcycle : NoNegativeCycle w) (i j : Fin n) :
    algorithm97 w i j = shortestLength w i j := by sorry

end FloydAlgorithms.ShortestPath
