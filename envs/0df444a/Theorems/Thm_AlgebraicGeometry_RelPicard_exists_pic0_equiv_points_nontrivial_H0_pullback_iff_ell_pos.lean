-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos
-- name    : AlgebraicGeometry.RelPicard.exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/a32e183b-b2ef-5ca3-bcf2-1fd37a7eae82
-- title:
--   Pic⁰ of the function field as k-points of J
-- statement:
--   Let $k$ be an algebraically closed field, $c : C \to \operatorname{Spec} k$ a proper, smooth of relative dimension one, geometrically integral morphism of schemes, and $\varepsilon$ a $k$-point of $C$, i.e. a morphism $\varepsilon_1 : \operatorname{Spec} k \to C$ with $\varepsilon_1$ followed by $c$ the identity. Let $J$ be a designation consisting of a scheme with a structure morphism `J.toBase` to $\operatorname{Spec} k$ and a zero section, and let $h$ witness that $J$ represents the functor of rigidified line bundles on $C$ relative to $\varepsilon$ that are fibrewise algebraically equivalent to zero: $h$ provides a Poincaré bundle `h.poincare` on the pullback of $c$ along `J.toBase`, the property that each such bundle on a base $t$ is the pullback of `h.poincare` along a unique section over $t$, and triviality along the zero section. Let $F$ be a field over $k$ with `IsCurveOver k F` (principal divisors of degree zero exist, all residue fields of places are finite over $k$, and $\Omega_{F/k}$ is free of rank one) and essentially of finite type over $k$; let $M$ be a curve model of $F$ over $k$, $e : M.C \cong C$ an isomorphism over $\operatorname{Spec} k$ (the forward map followed by $c$ is `M.toBase`), and $\varepsilon'$ a $k$-point of $M.C$ mapping to $\varepsilon_1$ under $e$. Endow the object $\operatorname{Over.mk}\,J.toBase$ with the group-object structure obtained from $h$ through the group-valued refinement `algEquivZeroGroupCut` of the fibrewise-algebraic-equivalence condition. Then there is a bijection $\mathrm{pts}$ from $\mathrm{Pic}^0(F/k)$, the degree-zero divisors modulo principal ones, onto the $k$-points of $J$, i.e. the morphisms $\operatorname{Over.mk}(\mathbf 1_{\operatorname{Spec} k}) \to \operatorname{Over.mk}\,J.toBase$, which carries addition to the group multiplication, and such that for every degree-zero divisor $Dv$, every $d \in \mathbb{N}$ and every cover of $C$ by two affine opens whose union is $C$ and whose intersection is affine, the two-chart Čech $H^0$ (the kernel of the difference of the two restriction maps on the product of the sections over the two opens) of the pullback of the Poincaré bundle along the morphism $C \to C \times_{\operatorname{Spec} k} J$ with components the identity and $c$ followed by $\mathrm{pts}(\,[Dv]\,)$, tensored with the inverse module of the $d$-th power of the ideal sheaf of $\varepsilon_1$, is nontrivial if and only if $\ell\big(Dv + d\,[\,\varepsilon'\,]\big) > 0$, where $\ell$ is the $k$-dimension of the Riemann–Roch space and $[\,\varepsilon'\,]$ is the place of $F/k$ corresponding to $\varepsilon'$ under the model $M$.
--
--   This is the dictionary between the group of $k$-points of the Jacobian of a pointed smooth proper geometrically integral curve and the degree-zero divisor class group of its function field, together with the translation of nonvanishing of $H^0$ of a twisted Poincaré bundle into positivity of the Riemann–Roch dimension $\ell$. It is used to obtain the corresponding statement in which the cohomology is read on the fibre of $C \times_k J \to J$ above the point, rather than on $C$ itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian AlgebraicCurve

open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.RelPicard.exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (J : RelativePic0Designation k c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)
    {F : Type u} [Field F] [Algebra k F] [IsCurveOver k F] [Algebra.EssFiniteType k F]
    (M : CurveModel k F) (e : M.C ≅ C) (he : e.hom ≫ c = M.toBase)
    (ε' : {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) (hε' : ε'.1 ≫ e.hom = ε.1) :
    letI := (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J from h).grpObj
    ∃ pts : Pic0 k F ≃ (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase),
      (∀ a b : Pic0 k F, pts (a + b) = pts a * pts b) ∧
      ∀ (Dv : Divisor.degZero (K := k) (F := F)) (d : ℕ) (𝒱 : C.TwoAffineOpenCover),
        Nontrivial (𝒱.sectionsOf c
          ((Scheme.Modules.pullback
              (pullback.lift (𝟙 C) (c ≫ (pts (Pic0.mk Dv)).left)
                (((Category.id_comp c).trans (Category.comp_id c).symm).trans
                  ((congrArg (c ≫ ·) (Over.w (pts (Pic0.mk Dv)))).symm.trans
                    (Category.assoc c _ _).symm)))).obj h.poincare.L ⊗
            ((ε.1.ker) ^ d).invModule)).H0 ↔
          0 < ell ((Dv : Divisor k F) + Finsupp.single (M.pointEquivPlace ε') (d : ℤ)) := by sorry
