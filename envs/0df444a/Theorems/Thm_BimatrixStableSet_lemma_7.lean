-- Prove2me | Theorems.Thm_BimatrixStableSet_lemma_7
-- name    : BimatrixStableSet.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:24.91873+00:00
-- url     : https://prove2.me/theorems/87c08638-8e5e-447e-b09c-9f206ae62bd2
-- title:
--   Lemma 7 — a non-neighborly $P$ with a facet of stable-set bound below 14
-- statement:
--   Let $(A,B)$ be a non-degenerate $5\times5$ game with best-response polytopes $P$ and $Q$. Suppose that $P$ is non-neighborly, that is, not dual-neighborly, and that $P$ has a facet $P_i$ with stable-set bound less than $14$. Then the game has at most $32$ equilibria, counting the artificial equilibrium $(0,0)$.
--
--   This closes the case of a facet with few facets in the proof of Theorem 5.
--
--   Differences from the source:
--   - encoding: the standing assumptions of the section, stated once → explicit hypotheses `HasBestResponsePolytopes A B` and `IsNondegenerate A B`; reason: same instances
--   - encoding: "at most $c$ equilibria" → `Set.encard` $\le c$ in $\mathbb N_\infty$; reason: finiteness is part of the claim, so no count of an infinite set collapses
--   - encoding: labels in $[m+n]$ → the type `Fin m ⊕ Fin n`, with label $i\le m$ as `Sum.inl` and label $m+j$ as `Sum.inr`; reason: same labels, zero-based
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Lemma 7, p.18

import Mathlib
import Definitions.Def_BimatrixStableSet_BestResponse
import Definitions.Def_BimatrixStableSet_PolytopeTypes

namespace BimatrixStableSet

/-- Lemma 7, p.18 (Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3): suppose `P` is non-neighborly
and has at least one facet `Pᵢ` with a stable-set bound of less than 14. Then the game has at most 32
equilibria.

**Formalization Note.** The standing assumptions of §6 are hypotheses: `m = n = 5`, the game is
non-degenerate, and `P`, `Q` are polytopes. "Non-neighborly" means not dual-neighborly, p.14. -/
theorem lemma_7 (A B : Matrix (Fin 5) (Fin 5) ℝ) (hPQ : HasBestResponsePolytopes A B)
    (hAB : IsNondegenerate A B)
    (hP : ¬ (bestResponseP B).IsDualNeighborly (bestResponseP B).carrier)
    (i : Fin 5 ⊕ Fin 5)
    (hi : (bestResponseP B).IsFacetOf ((bestResponseP B).face {i}) (bestResponseP B).carrier)
    (hb : (bestResponseP B).stableBound ((bestResponseP B).face {i}) < 14) :
    (equilibria A B).encard ≤ 32 := by sorry

end BimatrixStableSet
