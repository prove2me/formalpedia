-- Prove2me | Theorems.Thm_BimatrixStableSet_lemma_2
-- name    : BimatrixStableSet.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:51.03346+00:00
-- url     : https://prove2.me/theorems/684b695a-82df-44a8-ba6e-06dcc726da08
-- title:
--   Lemma 2 — dual-neighborly polytopes maximize vertices; the maxima are 20, 27, 30, 42
-- statement:
--   Let $d$ and $k$ be given. Among all $d$-polytopes with $k$ facets, a polytope with the largest number of vertices is simple and dual-neighborly. Likewise, among simple $d$-polytopes with $k$ facets, one with the largest number of vertices is dual-neighborly. Moreover, the maximal number of vertices of a polytope in $\mathcal P^4_8$, $\mathcal P^4_9$, $\mathcal P^5_9$, $\mathcal P^5_{10}$ is
--
--   $$
--   20,\quad 27,\quad 30,\quad 42,
--   $$
--
--   respectively; each value is an upper bound that is attained.
--
--   This is the case of the upper bound theorem that the proof of Theorem 5 uses to bound the vertices of $P$, $Q$ and their facets.
--
--   Differences from the source:
--   - generalization: a polytope in $\mathbb R^d$ → a bounded face, of dimension $d$, of a finite linear system in any $\mathbb R^N$; reason: every polytope is such a face (take $N=d$ and the whole polyhedron), and a facet of $P\subseteq\mathbb R^5$ is one without a change of coordinates
--   - reading: "only simple polytopes that are dual-neighborly have the largest numbers of vertices" → two clauses, one for maximizers among all polytopes (simple and dual-neighborly) and one for maximizers among simple polytopes (dual-neighborly); reason: the sentence can be read either way, and both readings are stated
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Lemma 2, p.6

import Mathlib
import Definitions.Def_BimatrixStableSet_PolytopeTypes

namespace BimatrixStableSet

/-- Lemma 2, p.6 (Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3): for a given dimension and
number of facets, only simple polytopes that are dual-neighborly have the largest numbers of
vertices. The maximal number of vertices of a polytope in `𝒫⁴₈`, `𝒫⁴₉`, `𝒫⁵₉`, `𝒫⁵₁₀` is
`20`, `27`, `30`, `42`, respectively.

**Formalization Note.** The first sentence is stated in both of its readings: among all
`d`-polytopes with `k` facets, and among the simple ones. For the second sentence, `IsGreatest` says
that the value is an upper bound and is attained. The polytopes are faces of bounded systems in any
`ℝᴺ`. -/
theorem lemma_2 :
    (∀ (d k : ℕ) (R : Realization), R.IsPolytopeWith d k →
      R.V ∈ upperBounds (polytopeVertexCounts d k) →
      R.Z.IsSimple R.F ∧ R.Z.IsDualNeighborly R.F) ∧
    (∀ (d k : ℕ) (R : Realization), R.IsSimplePolytope d k →
      R.V ∈ upperBounds (simpleVertexCounts d k) → R.Z.IsDualNeighborly R.F) ∧
    IsGreatest (simpleVertexCounts 4 8) 20 ∧
    IsGreatest (simpleVertexCounts 4 9) 27 ∧
    IsGreatest (simpleVertexCounts 5 9) 30 ∧
    IsGreatest (simpleVertexCounts 5 10) 42 := by sorry

end BimatrixStableSet
