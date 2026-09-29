-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_iso_pullback_unit_of_isAlgEquivZero_baseChange_of_curveModel_ratFunc
-- name    : AlgebraicGeometry.RelPicard.nonempty_pullback_iso_pullback_unit_of_isAlgEquivZero_baseChange_of_curveModel_ratFunc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/7f79f2dc-dbab-5538-824c-d1411cc32249
-- title:
--   Triviality on a rational model descends from Ω to k
-- statement:
--   Let $k$ be an algebraically closed field and $\Omega$ an algebraically closed field that is a $k$-algebra (both in the same universe). Let $X$ be a scheme with a morphism $x : X \to \operatorname{Spec} k$. Let $M$ be a `CurveModel` for $k \subseteq \operatorname{RatFunc} k$: an integral scheme $M.C$ with a proper morphism $M.\mathrm{toBase} : M.C \to \operatorname{Spec} k$ smooth of relative dimension $1$, a ring isomorphism from $\operatorname{RatFunc} k$ onto the function field of $M.C$ compatible with the map induced by the structure morphism, a bijection from the closed points of $M.C$ onto the places of $\operatorname{RatFunc} k$ over $k$ under which the image of each stalk is the corresponding valuation subring, and the property that every finite subset of $M.C$ lies in an affine open. Let $\mathcal{W}M$ be a two-affine open cover of $M.C$, i.e. two affine opens whose union is everything and whose intersection is affine. Let $i : M.C \to X$ satisfy $i$ followed by $x$ equals $M.\mathrm{toBase}$, and let $L$ be an $\mathcal{O}_X$-module that is invertible in the sense that every point of $X$ has an open neighbourhood $U$ with $L|_U$ isomorphic to the unit module of $U$. Write $X_\Omega = X \times_{\operatorname{Spec} k} \operatorname{Spec}\Omega$, with $x_\Omega$ its second projection and $L_\Omega$ the pullback of $L$ along its first projection. Assume $\mathrm{IsAlgEquivZero}$ holds for $x_\Omega$ and $L_\Omega$: there are a scheme $T'$ and a morphism $h : T' \to \operatorname{Spec}\Omega$ that is locally of finite type and geometrically integral, an invertible module $M'$ on $X_\Omega \times_{\operatorname{Spec}\Omega} T'$, and two sections $t_0, t_1$ of $h$, such that the restriction of $M'$ along the base change of $t_0$ is isomorphic to the unit module, while its restriction along the base change of $t_1$ is isomorphic to the pullback of $L_\Omega$. The conclusion is that the set of isomorphisms $i^{*}L \cong i^{*}\mathcal{O}_X$ in the category of $\mathcal{O}_{M.C}$-modules is nonempty (the target being the pullback along $i$ of the unit module of $X$, not the unit module of $M.C$ itself).
--
--   This is the descent step asserting that a line bundle which becomes algebraically equivalent to zero after base change to a larger algebraically closed field $\Omega$ restricts trivially to a genus-zero ($\operatorname{RatFunc} k$) curve mapping into $X$ over $k$. It is used in showing that the condition of algebraic equivalence to zero on a degenerate fibre built from two projective lines glued at points is independent of the chosen geometric point, via [`AlgebraicGeometry.RelPicard.isAlgEquivZero_fibre_of_range_subset_singleton_of_twoLineDegenerations`](thm.html#AlgebraicGeometry.RelPicard.isAlgEquivZero_fibre_of_range_subset_singleton_of_twoLineDegenerations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_iso_pullback_unit_of_isAlgEquivZero_baseChange_of_curveModel_ratFunc.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.nonempty_pullback_iso_pullback_unit_of_isAlgEquivZero_baseChange_of_curveModel_ratFunc
    (k : Type u) [Field k] [IsAlgClosed k] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (M : CurveModel k (RatFunc k)) (𝒲M : M.C.TwoAffineOpenCover) (i : M.C ⟶ X) (hi : i ≫ x = M.toBase)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hΩ : IsAlgEquivZero (pullback.snd x (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))
      ((Scheme.Modules.pullback (pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).obj L)) :
    Nonempty ((Scheme.Modules.pullback i).obj L ≅
      (Scheme.Modules.pullback i).obj (SheafOfModules.unit X.ringCatSheaf)) := by sorry
