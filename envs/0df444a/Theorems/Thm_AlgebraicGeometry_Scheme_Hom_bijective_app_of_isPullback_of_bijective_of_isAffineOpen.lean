-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen
-- name    : AlgebraicGeometry.Scheme.Hom.bijective_app_of_isPullback_of_bijective_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/3580e1ec-36e0-56ff-bbaf-f8473e4d8074
-- title:
--   Sections on U×_k Y when Γ(Y,𝒪_Y)=k
-- statement:
--   Let $k$ be a field and let $X$, $Y$, $P$ be schemes, with structure morphisms $f_X \colon X \to \operatorname{Spec} k$ and $f_Y \colon Y \to \operatorname{Spec} k$, where $f_Y$ is assumed quasi-compact and separated (as a morphism of schemes). Assume that the ring homomorphism on global sections obtained by composing the inverse of the canonical isomorphism $k \xrightarrow{\sim} \Gamma(\operatorname{Spec} k, \mathcal{O})$ with $f_Y^{\sharp}$ on the top open, i.e. the structural map $k \to \Gamma(Y, \mathcal{O}_Y)$, is bijective. Let $p_1 \colon P \to X$ and $p_2 \colon P \to Y$ be morphisms forming a pullback square over $\operatorname{Spec} k$, so that $p_1$ followed by $f_X$ equals $p_2$ followed by $f_Y$ and the square is cartesian; thus $P$ is a fibre product $X \times_k Y$ with its two projections. Finally let $U$ be an open subset of $X$ which is affine. The conclusion is that the ring homomorphism $p_1^{\sharp} \colon \Gamma(U, \mathcal{O}_X) \to \Gamma(p_1^{-1}U, \mathcal{O}_P)$ induced by $p_1$ on sections over $U$ is bijective.
--
--   This is the degree-zero case of flat base change over a field: for $Y$ quasi-compact and separated with $\Gamma(Y,\mathcal{O}_Y)=k$, the functions on $U\times_k Y$ are exactly those on $U$, for every affine open $U\subseteq X$. It is used in the comparison of sections of $\mathcal{O}$-module presheaves along such a base change, in [`AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.bijective_app_of_isPullback_of_bijective_of_isAffineOpen
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fY] [IsSeparated fY]
    (hY : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fY.appTop).hom)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (p₁.app U).hom := by sorry
