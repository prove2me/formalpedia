-- Prove2me | Theorems.Thm_EuclideanLineAvgDist_Embedding_matching_lipschitz_duality
-- name    : EuclideanLineAvgDist.Embedding.matching_lipschitz_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:15.061858+00:00
-- url     : https://prove2.me/theorems/de49ffe0-0e6f-45f3-a841-8a271872cced
-- title:
--   Lemma 3.1 — a minimum-weight matching is certified by a 1-Lipschitz potential
-- statement:
--   Let $(X,d)$ be a finite metric space and let $A,B\subseteq X$ be disjoint sets of equal size. If $M$ is a minimum-weight perfect matching between $A$ and $B$, with edge weights $d(x,y)$, then there exists a non-expansive $f:X\to\mathbb R$ such that
--   $$\sum_{y\in B}f(y)-\sum_{x\in A}f(x)=\sum_{(x,y)\in M}d(x,y).$$
--
--   This is a special case of Kantorovich–Rubinstein duality. In the proof of Theorem 1.1 it turns the matching of Corollary 2.2 into the embedding.
--
--   **Formalization Note** A perfect matching between $A$ and $B$ is a bijection $M:A\to B$, and $\sum_{(x,y)\in M}d(x,y)=\sum_{a\in A}d(a,M(a))$. Its existence already forces $|A|=|B|$, so equal size is not a separate hypothesis. The case $A=B=\emptyset$ is included. The conclusion asks for an actual function attaining the equality.
--
--   Differences from the source:
--   - encoding: $A,B$ of equal size and a perfect matching $M$ between them → a bijection $M:A\to B$; reason: a perfect matching between two sets is a bijection, whose existence is equivalent to equal size
--   - encoding: a metric space of size $n$ → a finite type with a metric; reason: same instances
-- source:
--   Jack Spalding-Jamieson, STOC 2027 submission #1643 (October 2026), p. 6, Lemma 3.1

import Mathlib
import Definitions.Def_EuclideanLineAvgDist_Embedding_Basic

open scoped BigOperators
set_option autoImplicit false

namespace EuclideanLineAvgDist.Embedding

/-- Lemma 3.1 (p. 6). Let `(X,d)` be a finite metric space and `A, B ⊆ X` disjoint subsets of equal
size. If `M` is a minimum-weight perfect matching between `A` and `B` (edge weights `d(x,y)`), then
there is a non-expansive `f : X → ℝ` with `∑_{y ∈ B} f(y) - ∑_{x ∈ A} f(x) = ∑_{(x,y) ∈ M} d(x,y)`.
(Equal size is implied by the existence of the bijection `M : A ≃ B`.) -/
theorem matching_lipschitz_duality {X : Type*} [MetricSpace X] [Fintype X]
    (A B : Finset X) (hdisj : Disjoint A B) (M : A ≃ B) (hM : IsMinMatching M) :
    ∃ f : X → ℝ, NonExpansive f ∧
      ∑ y ∈ B, f y - ∑ x ∈ A, f x = ∑ a : A, dist (a : X) (M a : X) := by sorry

end EuclideanLineAvgDist.Embedding
