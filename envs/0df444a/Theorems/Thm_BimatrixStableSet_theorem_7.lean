-- Prove2me | Theorems.Thm_BimatrixStableSet_theorem_7
-- name    : BimatrixStableSet.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:16.031571+00:00
-- url     : https://prove2.me/theorems/8ea071a2-5c3c-439d-a2e6-510c8bc7ef30
-- title:
--   Theorem 7 — stable-set bounds and obstruction vertices of the polytopes in $\mathcal P^4_9$
-- statement:
--   For every polytope $Q_i$ in $\mathcal P^4_9$:
--
--   1. the stable-set bound of $Q_i$ is at most $20$;
--   2. $Q_i$ has at least three obstruction vertices;
--   3. if $Q_i$ has stable-set bound $20$, then $Q_i$ does not have a 3-cube as a facet;
--   4. if $Q_i$ has stable-set bound $20$, then $Q_i$ has at least five obstruction vertices.
--
--   These facts control where the equilibrium vertices in $Q$ can be, in the case that a facet of $Q$ has nine facets. The paper obtains them by computer calculation from a known enumeration.
--
--   Differences from the source:
--   - generalization: polytopes in $\mathbb R^d$ → bounded faces of dimension $d$ of finite linear systems in any $\mathbb R^N$; reason: the case $N=d$ with the whole polyhedron is the source; the proof applies these results to facets of $P,Q\subseteq\mathbb R^5$
--   - reading: "at least $t$ obstruction vertices" → $t+b\le V$; reason: p.14 defines obstruction vertices as vertices that cannot be equilibrium vertices, and p.16 counts them as $V-b$ for a 4-polytope
--   - encoding: "Computer calculations show the following" → the four clauses only; reason: the phrase is the method of proof, not the claim
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Theorem 7, p.17

import Mathlib
import Definitions.Def_BimatrixStableSet_PolytopeTypes

namespace BimatrixStableSet

/-- Theorem 7, p.17 (Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3), for every polytope `Qᵢ`
in `𝒫⁴₉`:
(a) the stable-set bound of `Qᵢ` is at most 20;
(b) `Qᵢ` has at least three obstruction vertices;
(c) if `Qᵢ` has stable-set bound 20, then `Qᵢ` does not have a 3-cube as a facet;
(d) if `Qᵢ` has stable-set bound 20, then `Qᵢ` has at least five obstruction vertices.

**Formalization Note.** The paper establishes this by computer calculation; the claim itself is the
four clauses. "At least `t` obstruction vertices" is `t + b ≤ V`, following p.16. A facet is a
3-cube when its face lattice is that of `[0,1]³`. -/
theorem theorem_7 (R : Realization) (hR : R.IsSimplePolytope 4 9) :
    R.b ≤ 20 ∧
    3 + R.b ≤ R.V ∧
    (R.b = 20 → ∀ G, R.Z.IsFacetOf G R.F → ¬ R.Z.IsCubeType G 3) ∧
    (R.b = 20 → 5 + R.b ≤ R.V) := by sorry

end BimatrixStableSet
