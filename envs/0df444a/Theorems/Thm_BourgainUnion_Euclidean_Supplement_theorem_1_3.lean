-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_Supplement_theorem_1_3
-- name    : BourgainUnion.Euclidean.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:34:43.693091+00:00
-- url     : https://prove2.me/theorems/9ba2c956-3d74-47e2-8703-323832763a56
-- title:
--   Theorem 1.3 — $O(k^{0.895}\log k)$ distortion for unions of 1-strongly Euclidean sets
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for every integer $k\ge1$, every metric space $(X,d)$ and every cover $X=U_1\cup\dots\cup U_k$ in which each $U_i$ is 1-strongly Euclidean in $X$ (each $U_i\cup\{x\}$, $x\in X$, embeds isometrically into $\ell_2$). There is a map $F:X\to\ell_2$ and a factor $D$ with
--   $$1\le D\le C\,k^{0.895}\log(k+1),\qquad d(x,y)\le\|F(x)-F(y)\|\le D\,d(x,y)\quad(x,y\in X).$$
--   The space may be infinite and the sets may overlap or be empty.
--
--   Differences from the source:
--   - encoding: distortion O(k^0.895 log k) → one positive constant C, chosen before X, k and the cover, with D ≤ C·k^(179/200)·log(k+1), for k ≥ 1; reason: 0.895 = 179/200 exactly as printed; log(k+1) as in the base mission
--   - encoding: X embeds into ℓ2 with distortion D → a normalized embedding (published Embeds); reason: equation (1)
--   - encoding: a finite indexed cover X = U1 ∪ … ∪ Uk → U : Fin k → Set X with pointwise coverage, k ≥ 1; reason: zero-based indexing only; overlapping and empty members are permitted, as in the base goal
--   - encoding: real ℓ₂ → square-summable real sequences H2 = lp (fun _ : ℕ => ℝ) 2; reason: H2 is real ℓ₂, the published target of the base mission
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 2, §1.1, Theorem 1.3

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

open BourgainUnion.Euclidean

/-- Theorem 1.3, p. 2: one universal constant and the printed exponent 0.895 = 179/200. -/
theorem theorem_1_3 : ∃ C : ℝ, 0 < C ∧
    ∀ (X : Type) [MetricSpace X] (k : ℕ), 1 ≤ k →
      ∀ U : Fin k → Set X, Covers U → (∀ i, OneStrong (U i)) →
        ∃ D : ℝ, D ≤ C * (k:ℝ)^(179/200:ℝ) * Real.log (k+1) ∧ Embeds (X := X) D := by sorry

end BourgainUnion.Euclidean.Supplement
