-- Prove2me | Theorems.Thm_EvenCycleTuran_PathCount_upper_bound
-- name    : EvenCycleTuran.PathCount.upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:27:46.597378+00:00
-- url     : https://prove2.me/theorems/82977a95-4dde-4e67-9198-857915c86bef
-- title:
--   §7.2 — finite-size upper bound for l-vertex paths
-- statement:
--   Fix $k\ge1$ and $l\ge2$. If $G$ has $n>320(2k+1)$ vertices and no cycle of length $2k+1$, then
--
--   $$
--   \mathcal N(P_l,G)\le(n/2)^l.
--   $$
--
--   Here $P_l$ is a path on $l$ vertices and $\mathcal N$ counts unlabelled copies. This is the upper half of the asymptotic result in Theorem 23, with an explicit finite-size threshold.
--
--   **Formalization Note** The source's final display writes $P_1$, a typographical slip for $P_l$; the preceding display and Theorem 23 govern this statement.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 32, §7.2, final display of Theorem 23's proof

import Mathlib
import Definitions.Def_EvenCycleTuran_PathCount_Setting

namespace EvenCycleTuran.PathCount

/-- The finite-size upper bound at the end of the proof of Theorem 23. -/
theorem upper_bound (n k l : ℕ) (hk : 1 ≤ k) (hl : 2 ≤ l)
    (hn : 320 * (2 * k + 1) < n) (G : SimpleGraph (Fin n))
    (hfree : (SimpleGraph.cycleGraph (2 * k + 1)).Free G) :
    (G.copyCount (SimpleGraph.pathGraph l) : ℝ) ≤ ((n : ℝ) / 2) ^ l := by sorry

end EvenCycleTuran.PathCount
