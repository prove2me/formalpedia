-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_tangentPoints_appLE_eq_of_pointDerivations
-- name    : AlgebraicGeometry.exists_tangentPoints_appLE_eq_of_pointDerivations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/fbeb92bf-6ef4-5796-85c0-4de70df06f79
-- title:
--   Point derivations give dual-number tangent points
-- statement:
--   Let $K$ be a field, $X$ a scheme, $x : X \to \operatorname{Spec} K$ a morphism, $U$ an open subscheme of $X$ which is affine, and $eP : \operatorname{Spec} K \to U$ a morphism such that $eP$ followed by the inclusion $U \hookrightarrow X$ and then by $x$ is the identity of $\operatorname{Spec} K$. Let $M$ be an abelian group carrying compatible left and right $K$-module structures with central scalars. Write $\mathrm{ev} : \Gamma(X,U) \to K$ for the ring map obtained from $eP$ on global sections (the composite of `U.topIso.inv`, `eP.appTop` and `(Scheme.ΓSpecIso (CommRingCat.of K)).hom`), and give $\Gamma(X,U)$ the $K$-algebra structure `algebraOfHom x U` coming from $x$. Let $D$ be an element of [`Algebra.PointDerivations K Γ(X, U) ev M`](def/Algebra_PointDerivations.html#L9), that is a $K$-linear map $D : \Gamma(X,U) \to M$ satisfying $D(ab) = \mathrm{ev}(a)\cdot D(b) + \mathrm{ev}(b)\cdot D(a)$ for all $a,b$. Then there exists a morphism $v : \operatorname{Spec}(K \oplus M) \to X$, where $K \oplus M =$ `TrivSqZeroExt K M` is the trivial square-zero extension, such that $v$ followed by $x$ is $\operatorname{Spec}$ of the structure map $K \to K \oplus M$ and such that precomposing $v$ with $\operatorname{Spec}$ of the projection $K \oplus M \to K$ gives $eP$ followed by $U \hookrightarrow X$ (i.e. $v$ is an element of `TangentPoints x (eP ≫ U.ι) M`), together with a proof that $v^{-1}(U)$ is the whole of $\operatorname{Spec}(K \oplus M)$, and such that the resulting ring map $\Gamma(X,U) \to K \oplus M$ (the map `v.1.appLE U ⊤ hv` composed with `(Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K M))).hom`) sends each $r \in \Gamma(X,U)$ to $\mathrm{inl}(\mathrm{ev}\,r) + \mathrm{inr}(D\,r)$.
--
--   This is the classical identification of derivations at a rational point with points valued in dual numbers (here with values in an arbitrary module $M$ rather than $K$ itself), in the direction that produces a tangent point from a point derivation. It is used in the construction of the group law on a Jacobian with good reduction, where it feeds the relation [`GoodReductionJacobian.RelativeGroupLaw.pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero`](thm.html#GoodReductionJacobian.RelativeGroupLaw.pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_tangentPoints_appLE_eq_of_pointDerivations.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.exists_tangentPoints_appLE_eq_of_pointDerivations
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (U : X.Opens) (hU : IsAffineOpen U)
    (eP : Spec (CommRingCat.of K) ⟶ (U : Scheme.{u})) (heP : eP ≫ U.ι ≫ x = 𝟙 _)
    (M : Type u) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    (D : letI := algebraOfHom x U
      ↥(Algebra.PointDerivations K Γ(X, U) ((U.topIso.inv ≫ eP.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom) M)) :
    ∃ (v : TangentPoints x (eP ≫ U.ι) M) (hv : ⊤ ≤ v.1 ⁻¹ᵁ U),
      ∀ r : Γ(X, U),
        (v.1.appLE U ⊤ hv ≫ (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K M))).hom).hom r =
          TrivSqZeroExt.inl ((U.topIso.inv ≫ eP.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom r) +
            TrivSqZeroExt.inr (D.1 r) := by sorry
