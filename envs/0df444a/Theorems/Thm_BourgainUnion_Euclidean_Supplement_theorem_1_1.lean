-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_Supplement_theorem_1_1
-- name    : BourgainUnion.Euclidean.Supplement.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:34:19.604758+00:00
-- url     : https://prove2.me/theorems/0d75f8e7-0943-4746-9b41-060acc7ad7da
-- title:
--   Theorem 1.1 — $O(\log k)$ distortion for unions of 2-strongly Euclidean sets
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for every integer $k\ge1$, every metric space $(X,d)$ and every cover $X=U_1\cup\dots\cup U_k$ in which each $U_i$ is 2-strongly Euclidean in $X$. There is a map $F:X\to\ell_2$ and a factor $D$ with
--   $$1\le D\le C\log(k+1),\qquad d(x,y)\le\|F(x)-F(y)\|\le D\,d(x,y)\quad(x,y\in X).$$
--   The space may be infinite and the sets may overlap or be empty. When every $U_i$ is a single point this is Bourgain's theorem.
--
--   Differences from the source:
--   - encoding: distortion O(log k) → one positive constant C, chosen before X, k and the cover, with D ≤ C·log(k+1), for k ≥ 1; reason: the base mission's convention (Theorems 1.2, 1.4, 2.7); log(k+1) avoids log 1 = 0 at k = 1, where the source bound is a constant
--   - encoding: X embeds into ℓ2 with distortion D → a normalized embedding (published Embeds: 1 ≤ D, noncontracting, D-Lipschitz); reason: equation (1)
--   - encoding: a finite indexed cover X = U1 ∪ … ∪ Uk → U : Fin k → Set X with pointwise coverage, k ≥ 1; reason: zero-based indexing only; overlapping and empty members are permitted, as in the base goal
--   - encoding: V ∪ S Euclidean for every 2-element S ⊆ X → TwoStrong V: V Euclidean and V ∪ {x, y} Euclidean for all x, y ∈ X (x = y allowed); reason: equivalent: V ∪ {x} ⊆ V ∪ {x, y}, and when X has fewer than two points every subset is Euclidean
--   - encoding: real ℓ₂ → square-summable real sequences H2 = lp (fun _ : ℕ => ℝ) 2; reason: H2 is real ℓ₂, the published target of the base mission
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 2, §1.1, Theorem 1.1

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel
import Definitions.Def_BourgainUnion_Euclidean_Supplement_StrongModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

open BourgainUnion.Euclidean

/-- Theorem 1.1, p. 2: one universal constant; arbitrary spaces and overlapping covers. -/
theorem theorem_1_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (X : Type) [MetricSpace X] (k : ℕ), 1 ≤ k →
      ∀ U : Fin k → Set X, Covers U → (∀ i, TwoStrong (U i)) →
        ∃ D : ℝ, D ≤ C * Real.log (k+1) ∧ Embeds (X := X) D := by sorry

end BourgainUnion.Euclidean.Supplement
