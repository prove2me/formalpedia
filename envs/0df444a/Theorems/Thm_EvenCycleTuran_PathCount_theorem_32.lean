-- Prove2me | Theorems.Thm_EvenCycleTuran_PathCount_theorem_32
-- name    : EvenCycleTuran.PathCount.theorem_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:27:33.215982+00:00
-- url     : https://prove2.me/theorems/06df3e3b-d5b8-4274-9f47-c4e2a157cf5f
-- title:
--   Theorem 32 (Nikiforov) — spectral radius of a C_{2k+1}-free graph
-- statement:
--   Let $k\ge1$, and let $G$ be a graph on $n>320(2k+1)$ vertices containing no cycle of length $2k+1$. Its spectral radius satisfies
--
--   $$
--   \mu(G)\le\sqrt{n^2/4}.
--   $$
--
--   This external result supplies the uniform spectral bound used in Theorem 23. Its numerical threshold is part of the claim.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 32, Theorem 32 (attributed there to Nikiforov [34])

import Mathlib
import Definitions.Def_EvenCycleTuran_PathCount_Setting

namespace EvenCycleTuran.PathCount

/-- Nikiforov's spectral radius bound, quoted as Theorem 32. -/
theorem theorem_32 (n k : ℕ) (hk : 1 ≤ k) (hn : 320 * (2 * k + 1) < n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : (SimpleGraph.cycleGraph (2 * k + 1)).Free G) :
    specRad G ≤ Real.sqrt ((n : ℝ) ^ 2 / 4) := by sorry

end EvenCycleTuran.PathCount
