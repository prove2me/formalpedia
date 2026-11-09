-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_lemma_C_1
-- name    : BourgainUnion.Euclidean.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:44.098433+00:00
-- url     : https://prove2.me/theorems/2a1e2d6f-ea6e-4ef5-8e52-79271e2d1a42
-- title:
--   Lemma C.1 — finite subsets determine distortion
-- statement:
--   Let $(X,d)$ be a separable metric space and let $D\ge1$. Suppose every finite subset $S\subseteq X$ has a normalized embedding into real $\ell_2$ with that same factor $D$. Then there is a map $F:X\to\ell_2$ such that
--   $$d(x,y)\le\|F(x)-F(y)\|\le Dd(x,y)\qquad(x,y\in X).$$
--   This preserves the factor when passing from finite subsets to the entire space, including unbounded and incomplete spaces. No finite dimension bound is asserted.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: every finite subset S of X → every Finset S with its induced metric; reason: finite subsets are represented without identifying distinct ambient points
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 32, Lemma C.1

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Lemma C.1, pp.32--33: the same factor for every finite subset. -/
theorem lemma_C_1 (X : Type*) [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    (D : ℝ) (hD : 1 ≤ D)
    (hfinite : ∀ S : Finset X, Embeds (X := {x // x ∈ S}) D) :
    Embeds (X := X) D := by sorry

end BourgainUnion.Euclidean
