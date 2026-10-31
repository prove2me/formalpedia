-- Prove2me | Theorems.Thm_BimatrixStableSet_display_8
-- name    : BimatrixStableSet.display_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:44.528985+00:00
-- url     : https://prove2.me/theorems/229c0f30-d622-4466-a5ea-c42bb317447a
-- title:
--   Display (8) — the 37 types of $\mathcal P^4_8$ with their pairs $(V,b)$; the 4-cube and the semi-cube
-- statement:
--   There are exactly 37 combinatorial types of polytopes in $\mathcal P^4_8$, and they can be listed in an order in which the pairs $(V,b)$ of number of vertices and stable-set bound are those of display (8). The 4-cube is number 24 of that list, with $(V,b)=(16,16)$, and it is the only type with this pair. The semi-cube is number 23, with $(V,b)=(17,14)$, and it is the only type with this pair. Every polytope in $\mathcal P^4_8$ that is neither a 4-cube nor a semi-cube satisfies
--
--   $$
--   4+b\le V,
--   $$
--
--   that is, it has at least four obstruction vertices.
--
--   This table bounds the equilibrium vertices on the two disjoint facets of a non-neighborly $P$ with at most 8 facets. The paper obtains it by computer calculation from a known enumeration.
--
--   Differences from the source:
--   - generalization: polytopes in $\mathbb R^d$ → bounded faces of dimension $d$ of finite linear systems in any $\mathbb R^N$; reason: the case $N=d$ with the whole polyhedron is the source; the proof applies these results to facets of $P,Q\subseteq\mathbb R^5$
--   - reading: "at least $t$ obstruction vertices" → $t+b\le V$; reason: p.14 defines obstruction vertices as vertices that cannot be equilibrium vertices, and p.16 counts them as $V-b$ for a 4-polytope
--   - encoding: the numbering of Firsching (2017) → some ordering of the 37 types realizes the table, in the order of the page; reason: the numbering has no meaning in Lean, and every pair and its multiplicity is kept
--   - reading: "a type with 17 vertices that has only 3 obstruction vertices" → `IsSemiCube`: a polytope in $\mathcal P^4_8$ with $(V,b)=(17,14)$, and the statement that this determines one type; reason: $3$ obstruction vertices means $V-b=3$ (p.16), and the only such row with $V=17$ is number 23
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, §6, pp.15–17, display (8)

import Mathlib
import Definitions.Def_BimatrixStableSet_PolytopeTypes

namespace BimatrixStableSet

/-- Display (8) with its surrounding text, pp.15–17 (Ickstadt, Theobald, von Stengel,
arXiv:2411.12385v3): there are 37 combinatorial types of polytopes in `𝒫⁴₈`, with the pairs `(V, b)`
of the table. The cube is number 24 and the semi-cube is number 23 (indices 23 and 22 of `Fin 37`).
Every other type has at least four obstruction vertices.

**Formalization Note.** `rep` is a list of the types in the order of the page. Firsching's numbering
has no meaning in Lean, so the statement says that some ordering of the types realizes the table.
"At least four obstruction vertices" is `4 + b ≤ V`, following p.16 ("The number `V − b` of
obstruction vertices"). -/
theorem display_8 :
    ∃ rep : Fin 37 → Realization, IsTypeList 4 8 table8 rep ∧
      (∀ i, (rep i).IsCube 4 ↔ i = 23) ∧
      (∀ R : Realization, R.IsSimplePolytope 4 8 →
        ((R.IsCube 4 ↔ (R.V, R.b) = (16, 16)) ∧
         (IsSemiCube R ↔ R.SameType (rep 22)) ∧
         (¬ R.IsCube 4 → ¬ IsSemiCube R → 4 + R.b ≤ R.V))) := by sorry

end BimatrixStableSet
