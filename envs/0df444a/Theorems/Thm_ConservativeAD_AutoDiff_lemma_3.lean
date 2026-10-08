-- Prove2me | Theorems.Thm_ConservativeAD_AutoDiff_lemma_3
-- name    : ConservativeAD.AutoDiff.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:42:10.847216+00:00
-- url     : https://prove2.me/theorems/fc9e9324-3367-454e-9eb9-2751e4e9d371
-- title:
--   Lemma 3 — componentwise aggregation of conservative fields is a conservative mapping
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^m$ be locally Lipschitz, and for each $i=1,\dots,m$ let $D_i$ be a conservative field for the $i$-th coordinate $F_i$ of $F$. Define $J_F:\mathbb R^n\rightrightarrows\mathbb R^{m\times n}$ by
--
--   $$
--   J_F(x)=\left\{\begin{pmatrix}v_1^T\\ \vdots\\ v_m^T\end{pmatrix} : v_i\in D_i(x),\ i=1,\dots,m\right\}.
--   $$
--
--   Then $J_F$ is a conservative mapping for $F$.
--
--   Stacking conservative fields of the coordinates yields a generalized Jacobian; this is how the elementary operations of a program get their conservative mappings.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 13, Lemma 3

import Mathlib
import Definitions.Def_ConservativeAD_AutoDiff_ConservativeField
import Definitions.Def_ConservativeAD_AutoDiff_ConservativeMap

namespace ConservativeAD.AutoDiff

/-- Lemma 3 (componentwise aggregation), p. 13. If `F : ℝ^n → ℝ^m` is locally Lipschitz and, for
each `i`, `D_i` is a conservative field for the `i`-th coordinate of `F`, then
`J_F(x) = { matrices with rows v_1ᵀ, …, v_mᵀ : v_i ∈ D_i(x) }` is a conservative mapping for `F`. -/
theorem lemma_3 {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hF : LocallyLipschitz F)
    (Ds : Fin m → EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hDs : ∀ i, ConservativeAD.GradAE.IsPotential (Ds i) (fun x => F x i)) :
    IsConservativeMap F
      (fun x => {V : Matrix (Fin m) (Fin n) ℝ | ∀ i, WithLp.toLp 2 (V i) ∈ Ds i x}) := by sorry

end ConservativeAD.AutoDiff
