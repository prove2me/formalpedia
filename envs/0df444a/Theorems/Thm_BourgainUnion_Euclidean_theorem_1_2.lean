-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_theorem_1_2
-- name    : BourgainUnion.Euclidean.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:50.004839+00:00
-- url     : https://prove2.me/theorems/d94e1c02-93ed-4770-9b61-c2515d96e86d
-- title:
--   Theorem 1.2 — polynomial distortion and strict two-set bound
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for every integer $k\ge1$, every metric space $(X,d)$ and every cover $U_1,\ldots,U_k$ of $X$ by Euclidean subsets. Each $U_i$ is required only to admit an isometric embedding into real $\ell_2$; overlaps and empty members are allowed. There are a map $F:X\to\ell_2$ and factor $D$ such that
--   $$1\le D\le Ck^{141/125}\log(k+1),\qquad d(x,y)\le\|F(x)-F(y)\|\le Dd(x,y)\quad(x,y\in X).$$
--   Moreover, whenever $k=2$, there is a normalized embedding, possibly a different map, with factor
--   $$1\le D<3997/1000.$$
--   These conclusions apply to arbitrary infinite, unbounded, incomplete metric spaces. No separability, extension, terminal-map, energy or one-point Euclidean hypothesis is imposed. The universal constant precedes all instance parameters. This is the full Theorem 1.2, with both of its conclusions in one declaration.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: a finite indexed cover that may overlap → U : Fin k → Set X and pointwise coverage; reason: zero-based indexing only; overlap and empty members are permitted unless nonemptiness is stated
--   - encoding: O(k^1.128 log k) → one positive universal constant times k^(141/125) log(k+1), for k≥1; reason: 1.128=141/125 exactly; log(k+1) is the boundary convention of Theorems 1.4 and 2.7, recovering distortion one at k=1
--   - encoding: c₂(X)<3.997 in the two-set clause → an actual normalized embedding with D<3997/1000; reason: the source defines distortion by normalized embeddings; the uniform strict certificate in Appendix B and Lemma C.1 justify direct existence rather than an infimum-only formulation
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 2, Theorem 1.2

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Theorem 1.2 in full: the universal exponent and the strict two-set clause. -/
theorem theorem_1_2 : ∃ C : ℝ, 0 < C ∧
    ∀ (X : Type) [MetricSpace X] (k : ℕ), 1 ≤ k →
      ∀ U : Fin k → Set X, Covers U → (∀ i, IsEuclidean (U i)) →
        (∃ D : ℝ, D ≤ C*(k:ℝ)^(141/125:ℝ)*Real.log (k+1) ∧ Embeds (X := X) D) ∧
        (k = 2 → ∃ D : ℝ, D < (3997/1000:ℝ) ∧ Embeds (X := X) D) := by sorry

end BourgainUnion.Euclidean
