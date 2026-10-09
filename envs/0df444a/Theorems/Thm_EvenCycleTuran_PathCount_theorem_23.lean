-- Prove2me | Theorems.Thm_EvenCycleTuran_PathCount_theorem_23
-- name    : EvenCycleTuran.PathCount.theorem_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:27:41.457527+00:00
-- url     : https://prove2.me/theorems/af2c6485-170b-4865-a8ef-47fc874f0ae9
-- title:
--   Theorem 23 — asymptotic maximum number of paths in a C_{2k+1}-free graph
-- statement:
--   Fix integers $k\ge1$ and $l\ge2$. Among all graphs on $n$ vertices with no cycle of length $2k+1$, the maximum number of unlabelled copies of the path $P_l$ on $l$ vertices satisfies, as $n\to\infty$,
--
--   $$
--   \operatorname{ex}(n,P_l,C_{2k+1})=(1+o(1))(n/2)^l.
--   $$
--
--   Thus the balanced complete bipartite construction has the correct leading term. The claim includes both an asymptotic lower bound and an upper bound.
--
--   **Formalization Note** The $o(1)$ term is a real sequence tending to zero with $k,l$ fixed before $n$. The exact equality holds for all sufficiently large $n$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 8, Theorem 23 (restated on p. 32)

import Mathlib
import Definitions.Def_EvenCycleTuran_PathCount_Setting

namespace EvenCycleTuran.PathCount

/-- The maximum number of `l`-vertex paths in an odd-cycle-free graph, Theorem 23. -/
theorem theorem_23 (k l : ℕ) (hk : 1 ≤ k) (hl : 2 ≤ l) :
    ∃ ε : ℕ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ᶠ n in Filter.atTop,
        (EvenCycleTuran.C4Count.exCyc n (SimpleGraph.pathGraph l) {2 * k + 1} : ℝ) =
          (1 + ε n) * ((n : ℝ) / 2) ^ l := by sorry

end EvenCycleTuran.PathCount
