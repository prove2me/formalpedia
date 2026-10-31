-- Prove2me | Theorems.Thm_BimatrixStableSet_theorem_6
-- name    : BimatrixStableSet.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:04.809957+00:00
-- url     : https://prove2.me/theorems/cb9e8c25-92ce-479d-bd85-a7153ffb6eba
-- title:
--   Theorem 6 — dual-neighborly $P$ or $Q$ gives at most 32 equilibria
-- statement:
--   Let $(A,B)$ be a non-degenerate $5\times5$ game with best-response polytopes $P$ and $Q$. If $P$ or $Q$ is dual-neighborly, then the game has at most $32$ equilibria, counting the artificial equilibrium $(0,0)$.
--
--   This is the first of the two cases in the proof of Theorem 5. The paper's proof is a computer enumeration of the known combinatorial types.
--
--   Differences from the source:
--   - encoding: the standing assumptions of the section, stated once → explicit hypotheses `HasBestResponsePolytopes A B` and `IsNondegenerate A B`; reason: same instances
--   - encoding: "at most $c$ equilibria" → `Set.encard` $\le c$ in $\mathbb N_\infty$; reason: finiteness is part of the claim, so no count of an infinite set collapses
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Theorem 6, p.14

import Mathlib
import Definitions.Def_BimatrixStableSet_BestResponse

namespace BimatrixStableSet

/-- Theorem 6, p.14 (Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3): consider the best-response
polytopes `P` and `Q` for a `5 × 5` game. If `P` or `Q` is dual-neighborly, then the game has at most
32 equilibria.

**Formalization Note.** Non-degeneracy is the paper's standing assumption (pp.2, 5). "Equilibria" are
those of Definition 1, so `(0, 0)` is counted. The paper's proof is a computer enumeration; the
assumption that `P` and `Q` have ten facets (p.14) is a reduction made in that proof and is not a
hypothesis here. -/
theorem theorem_6 (A B : Matrix (Fin 5) (Fin 5) ℝ) (hPQ : HasBestResponsePolytopes A B)
    (hAB : IsNondegenerate A B)
    (hdn : (bestResponseP B).IsDualNeighborly (bestResponseP B).carrier ∨
      (bestResponseQ A).IsDualNeighborly (bestResponseQ A).carrier) :
    (equilibria A B).encard ≤ 32 := by sorry

end BimatrixStableSet
