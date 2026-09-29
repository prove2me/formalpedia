-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one
-- name    : AlgebraicGeometry.exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/228f4cb2-e4f8-543e-82db-c19d45bb7188
-- title:
--   Codimension-one points after a birational modification of a proper target
-- statement:
--   Let $k$ be a field and let $X$, $Y$ be schemes over $\operatorname{Spec} k$ via morphisms $f_X : X \to \operatorname{Spec} k$ and $f_Y : Y \to \operatorname{Spec} k$, with $X$ integral, $f_X$ locally of finite type and quasi-compact, $Y$ integral and $f_Y$ proper. Let $U \subseteq X$ be an open subscheme and $\alpha : U \to Y$ a morphism with $\alpha$ followed by $f_Y$ equal to the open immersion $U \hookrightarrow X$ followed by $f_X$, and assume the underlying continuous map of $\alpha$ has dense range. Let $z \in X$ lie in $U$ and assume $\mathcal{O}_{X,z}$ has Krull dimension $1$ and is integrally closed, while $\mathcal{O}_{Y,\alpha(z)}$ has Krull dimension $\neq 0$. Then there exist a scheme $Y'$ and a morphism $f_{Y'} : Y' \to \operatorname{Spec} k$ with $Y'$ integral and $f_{Y'}$ proper, a morphism $\beta : Y' \to Y$ with $\beta$ followed by $f_Y$ equal to $f_{Y'}$, an open $W \subseteq Y$ whose underlying set is dense and such that the restriction $\beta \mid_W$ is an isomorphism, an open $U' \leq U$ containing $z$, and a morphism $\alpha' : U' \to Y'$ with $\alpha'$ followed by $\beta$ equal to the inclusion $U' \hookrightarrow U$ followed by $\alpha$, such that $\mathcal{O}_{Y',\alpha'(z)}$ has Krull dimension $1$.
--
--   This is Rosenlicht's lemma on the extension of dominant rational maps into proper varieties: a codimension-one point of a normal locus of $X$ can be made to map to a codimension-one point after replacing the proper target by a modification that is an isomorphism over a dense open. It is used in the construction of a partial group action on a scheme with good reduction, through [`GoodReductionJacobian.PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one`](thm.html#GoodReductionJacobian.PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one
    {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [IsIntegral X] [LocallyOfFiniteType fX] [QuasiCompact fX] [IsIntegral Y] [IsProper fY]
    (U : X.Opens) (α : (U : Scheme.{u}) ⟶ Y) (hα : α ≫ fY = U.ι ≫ fX) (hdom : DenseRange α.base)
    (z : X) (hzU : z ∈ U) (hz₁ : ringKrullDim (X.presheaf.stalk z) = 1)
    (hzn : IsIntegrallyClosed (X.presheaf.stalk z))
    (hnd : ringKrullDim (Y.presheaf.stalk (α.base ⟨z, hzU⟩)) ≠ 0) :
    ∃ (Y' : Scheme.{u}) (fY' : Y' ⟶ Spec (.of k)) (_ : IsIntegral Y') (_ : IsProper fY')
      (β : Y' ⟶ Y) (_ : β ≫ fY = fY') (W : Y.Opens) (_ : Dense (W : Set ↥Y)) (_ : IsIso (β ∣_ W))
      (U' : X.Opens) (hU' : U' ≤ U) (hzU' : z ∈ U')
      (α' : (U' : Scheme.{u}) ⟶ Y') (_ : α' ≫ β = X.homOfLE hU' ≫ α),
      ringKrullDim (Y'.presheaf.stalk (α'.base ⟨z, hzU'⟩)) = 1 := by sorry
