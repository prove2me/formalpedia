-- Prove2me | Theorems.Thm_BimatrixStableSet_display_9
-- name    : BimatrixStableSet.display_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:50.235488+00:00
-- url     : https://prove2.me/theorems/e45429aa-8dd9-4297-a3c2-53dea094e51a
-- title:
--   Display (9) — the types of $\mathcal P^4_7$, $\mathcal P^4_6$ and $\mathcal P^4_5$
-- statement:
--   There are exactly five combinatorial types in $\mathcal P^4_7$, and their pairs $(V,b)$ are
--
--   $$
--   (14,10),\quad(13,8),\quad(12,8),\quad(12,8),\quad(11,6),
--   $$
--
--   so each has at least four obstruction vertices. There are exactly two types in $\mathcal P^4_6$, with pairs $(9,6)$ and $(8,4)$. There is exactly one type in $\mathcal P^4_5$, with pair $(5,2)$, and every polytope in $\mathcal P^4_5$ is a 4-dimensional simplex.
--
--   These facts rule out the facets of $P$ with fewer than eight facets in the proof of Theorem 5, apart from the cases of Lemma 7.
--
--   Differences from the source:
--   - generalization: polytopes in $\mathbb R^d$ → bounded faces of dimension $d$ of finite linear systems in any $\mathbb R^N$; reason: the case $N=d$ with the whole polyhedron is the source; the proof applies these results to facets of $P,Q\subseteq\mathbb R^5$
--   - reading: "at least $t$ obstruction vertices" → $t+b\le V$; reason: p.14 defines obstruction vertices as vertices that cannot be equilibrium vertices, and p.16 counts them as $V-b$ for a 4-polytope
--   - encoding: the sentence "at most nine vertices" for $\mathcal P^4_6$ → the two pairs $(9,6)$ and $(8,4)$; reason: the bound is immediate from them
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, §6, p.17, display (9)

import Mathlib
import Definitions.Def_BimatrixStableSet_PolytopeTypes

namespace BimatrixStableSet

/-- Display (9) and the sentences around it, p.17 (Ickstadt, Theobald, von Stengel,
arXiv:2411.12385v3): there are five combinatorial types in `𝒫⁴₇`, with the pairs `(V, b)` of (9), each
with at least four obstruction vertices. There are two types in `𝒫⁴₆`, with pairs `(9, 6)` and
`(8, 4)`. The only polytope in `𝒫⁴₅` is the 4-dimensional simplex, with `(V, b) = (5, 2)`.

**Formalization Note.** A simplex is the convex hull of affinely independent points, p.5, stated for
the polytope itself. The bound "at most nine vertices" for `𝒫⁴₆` is immediate from the two pairs. -/
theorem display_9 :
    (∃ rep : Fin 5 → Realization, IsTypeList 4 7 table9 rep) ∧
    (∀ R : Realization, R.IsSimplePolytope 4 7 → 4 + R.b ≤ R.V) ∧
    (∃ rep : Fin 2 → Realization, IsTypeList 4 6 ![(9, 6), (8, 4)] rep) ∧
    (∃ rep : Fin 1 → Realization, IsTypeList 4 5 ![(5, 2)] rep) ∧
    (∀ R : Realization, R.IsSimplePolytope 4 5 →
      ∃ v : Fin 5 → (Fin R.N → ℝ), AffineIndependent ℝ v ∧ R.F = convexHull ℝ (Set.range v)) := by sorry

end BimatrixStableSet
