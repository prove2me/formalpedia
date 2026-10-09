-- Prove2me | Theorems.Thm_EvenCycleTuran_PathCount_lower_bound
-- name    : EvenCycleTuran.PathCount.lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:27:40.169137+00:00
-- url     : https://prove2.me/theorems/73595646-bdd1-43ed-bdd7-e94a163028ba
-- title:
--   §7.2 — balanced complete bipartite lower bound for path copies
-- statement:
--   Fix $k\ge1$ and $l\ge2$. Let $B_n$ be the complete bipartite graph on $n$ vertices with parts of sizes $\lfloor n/2\rfloor$ and $\lceil n/2\rceil$. It contains no cycle of length $2k+1$. Its number of unlabelled copies of the path $P_l$ on $l$ vertices satisfies, as $n\to\infty$,
--
--   $$
--   \mathcal N(P_l,B_n)\ge(1+o(1))\left(\frac n2\right)^l.
--   $$
--
--   This construction gives the lower bound used in Theorem 23.
--
--   **Formalization Note** For odd $n$, the two part sizes differ by one. The $o(1)$ term is a real sequence tending to zero, chosen after $k,l$ and before $n$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 32, §7.2, first paragraph of Theorem 23's proof

import Mathlib
import Definitions.Def_EvenCycleTuran_PathCount_Setting

namespace EvenCycleTuran.PathCount

/-- The balanced complete bipartite construction gives the asymptotic lower
bound in the proof of Theorem 23. -/
theorem lower_bound (k l : ℕ) (hk : 1 ≤ k) (hl : 2 ≤ l) :
    (∀ n : ℕ, EvenCycleTuran.C4Count.CycleFree {2 * k + 1}
      (bipGraph n (n / 2))) ∧
    ∃ ε : ℕ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ᶠ n in Filter.atTop,
        (1 + ε n) * ((n : ℝ) / 2) ^ l ≤
          ((bipGraph n (n / 2)).copyCount (SimpleGraph.pathGraph l) : ℝ) := by sorry

end EvenCycleTuran.PathCount
