-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_lemma_4_4
-- name    : ConstrainedDirSep.STSep.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:05:16.000735+00:00
-- url     : https://prove2.me/theorems/e13ca090-14a0-42b8-8b09-35bd0ae0c18c
-- title:
--   Lemma 4.4 — r-partite graphs with two increasing chains between parts are 4(r − 1)-degenerate
-- statement:
--   Let $J$ be a finite simple graph with at least one vertex, and let $V(J)=V_1\cup\dots\cup V_r$ be a partition into parts (some possibly empty) such that every edge joins two different parts, each part being linearly ordered. Suppose that for every $i<j$ the edges between $V_i$ and $V_j$, viewed as points $(u,v)\in V_i\times V_j$ under the coordinatewise order, can be covered by at most two increasing chains. Then $J$ is $4(r-1)$-degenerate: every nonempty set $S$ of vertices contains a vertex with at most $4(r-1)$ neighbours in $S$.
--
--   Applied to the conflict graph of a Chain CSP instance, this bounds its degeneracy by $4(r-1)$, which Theorem 4.8 combines with independence covering families.
--
--   Differences from the source:
--   - encoding: parts V_1, …, V_r each linearly ordered → the parts are the fibres of a map to {0, …, r−1}, and one linear order on V(J) restricts to the order of each part; reason: any family of linear orders on disjoint parts extends to a linear order of their union.
--   - encoding: "d-degenerate: every nonempty subgraph has a vertex of degree at most d" → the published ForestBackdoorFPT.IsDegenerate (every nonempty vertex set has a vertex with at most d neighbours inside it); reason: equivalent, since a subgraph on S has degrees at most those of the induced subgraph.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 16 (PDF 19), Lemma 4.4 (proof p. 41, PDF 44)

import Mathlib
import Definitions.Def_ForestBackdoorFPT_IsDegenerate

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 16 (PDF 19), Lemma 4.4: a nonempty `r`-partite graph with linearly ordered
parts, whose edges between `V_i` and `V_j` (`i < j`) are covered by at most two increasing chains
of `V_i × V_j`, is `4(r − 1)`-degenerate.

The parts are the fibres of `part : V → Fin r`; the linear orders of the parts are the
restrictions of the linear order of `V`. -/
theorem lemma_4_4 {V : Type*} [Fintype V] [LinearOrder V] [Nonempty V] (r : ℕ)
    (J : SimpleGraph V) (part : V → Fin r)
    (hpart : ∀ u v : V, J.Adj u v → part u ≠ part v)
    (hchains : ∀ i j : Fin r, i < j → ∃ C₁ C₂ : Set (V × V),
      (∀ x ∈ C₁, ∀ y ∈ C₁, (x.1 ≤ y.1 ∧ x.2 ≤ y.2) ∨ (y.1 ≤ x.1 ∧ y.2 ≤ x.2)) ∧
      (∀ x ∈ C₂, ∀ y ∈ C₂, (x.1 ≤ y.1 ∧ x.2 ≤ y.2) ∨ (y.1 ≤ x.1 ∧ y.2 ≤ x.2)) ∧
      ∀ u v : V, part u = i → part v = j → J.Adj u v → (u, v) ∈ C₁ ∨ (u, v) ∈ C₂) :
    ForestBackdoorFPT.IsDegenerate J (4 * (r - 1)) := by sorry

end ConstrainedDirSep.STSep
