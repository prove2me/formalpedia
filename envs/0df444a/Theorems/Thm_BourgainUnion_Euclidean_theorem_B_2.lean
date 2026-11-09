-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_theorem_B_2
-- name    : BourgainUnion.Euclidean.theorem_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:56.295385+00:00
-- url     : https://prove2.me/theorems/d5ab913c-ca68-4016-a962-46f3e3a2d40f
-- title:
--   Theorem B.2 — both explicit two-set bounds
-- statement:
--   Let $X$ be any metric space covered by two subsets $U_1,U_2$. If both are Euclidean in $X$, there is a normalized embedding $F:X\to\ell_2$ with factor $D$ satisfying
--   $$1\le D<3997/1000=3.997.$$
--   If both are one-point strongly Euclidean in $X$, there is a normalized embedding with
--   $$1\le D\le193/50=3.86.$$
--   The cover may overlap, may have empty members and may be infinite. The strict inequality in the first conclusion and the non-strict inequality in the second are retained. This milestone supplies the second goal clause as well as the paper's additional one-point conclusion.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: a finite indexed cover that may overlap → U : Fin k → Set X and pointwise coverage; reason: zero-based indexing only; overlap and empty members are permitted unless nonemptiness is stated
--   - encoding: bounds on the smallest distortion c₂(X) → existence of normalized embeddings at the stated strict or non-strict bounds; reason: Appendix C transfers uniform finite bounds to actual embeddings; p. 32 supplies a squared factor below 15.975 for the strict clause and the fixed factor 3.86 for the second
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 31, Theorem B.2; proof p. 32

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Theorem B.2: both exact constants, both clauses, arbitrary metric spaces. -/
theorem theorem_B_2 (X : Type*) [MetricSpace X] (U : Fin 2 → Set X) (hcover : Covers U) :
    ((∀ i, IsEuclidean (U i)) →
      ∃ D : ℝ, D < (3997/1000 : ℝ) ∧ Embeds (X := X) D) ∧
    ((∀ i, OneStrong (U i)) →
      ∃ D : ℝ, D ≤ (193/50 : ℝ) ∧ Embeds (X := X) D) := by sorry

end BourgainUnion.Euclidean
