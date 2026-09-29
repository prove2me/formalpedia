-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_iff_ell_pos
-- name    : AlgebraicGeometry.RelPicard.exists_pic0_equiv_points_nontrivial_H0_iff_ell_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/67ad0366-3936-5996-83b9-f3c29737832b
-- title:
--   Theta dictionary: Pic⁰(F) and k-points of J
-- statement:
--   Let $k$ be an algebraically closed field and let $c : C \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, with a section $\varepsilon$ (a morphism $\operatorname{Spec} k \to C$ over the identity). Let $J$ consist of a scheme with structure morphism $J.\mathrm{toBase}$ to $\operatorname{Spec} k$ together with a zero section, and let $h$ witness that $J$ represents the subfunctor of rigidified line bundles on $C \times_k T$ cut out by the condition that all geometric fibres are algebraically equivalent to zero: $h$ provides a Poincaré rigidified bundle $h.\mathrm{poincare}$ on $C \times_k J$ in that class, the universal property, and the triviality of its restriction along the zero section. Let $F$ be a field extension of $k$ which is a curve over $k$ (principal divisors of degree zero exist, residue fields of places are finite over $k$, and $\Omega_{F/k}$ is free of rank one) and essentially of finite type over $k$, and let $M$ be a curve model of $F/k$, $e : M.C \cong C$ an isomorphism with $e \text{ followed by } c = M.\mathrm{toBase}$, and $\varepsilon'$ a section of $M.\mathrm{toBase}$ carried to $\varepsilon$ by $e$. Then, for the group-object structure on $J$ over $\operatorname{Spec} k$ obtained from representability of the cut as a presheaf of commutative groups, there is a bijection $\mathrm{pts}$ from $\mathrm{Pic}^0(F/k)$ — degree-zero divisors, i.e. finitely supported $\mathbb{Z}$-valued functions on places of $F/k$ of degree $0$, modulo principal ones — onto the set of morphisms $\operatorname{Spec} k \to J$ over $\operatorname{Spec} k$, such that $\mathrm{pts}(a+b) = \mathrm{pts}(a)\cdot \mathrm{pts}(b)$, and such that for every degree-zero divisor $D$ and every $d \in \mathbb{N}$ the following are equivalent: for every two-chart affine open cover of the fibre $C \times_J \{x\}$ at $x = \mathrm{pts}([D])$, the two-chart Čech $H^0$ (the kernel of the Čech differential) of the restriction to that fibre of $h.\mathrm{poincare}$ tensored with the dual of the $d$-th power of the ideal sheaf of the section — the twist by $d\varepsilon$ — is nontrivial; and $\ell\bigl(D + d\,[\varepsilon']\bigr) > 0$, where $\ell$ is the $k$-dimension of the Riemann–Roch space and $[\varepsilon']$ is the place of $F/k$ corresponding to $\varepsilon'$ under the model $M$.
--
--   This is the dictionary between the scheme-theoretic Jacobian and the function-field description of divisor classes: $k$-points of $J$ are identified as a group with $\mathrm{Pic}^0$ of $F/k$, and nonvanishing of $H^0$ of the Poincaré bundle on a fibre twisted by $d\varepsilon$ is read off from the Riemann–Roch dimension $\ell(D + d[\varepsilon'])$. It feeds the construction of a nonzero theta section and the triviality of the stabiliser of its zero locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_iff_ell_pos.lean

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

theorem AlgebraicGeometry.RelPicard.exists_pic0_equiv_points_nontrivial_H0_iff_ell_pos
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
      ∀ (Dv : Divisor.degZero (K := k) (F := F)) (d : ℕ),
        (∀ 𝒲 : (pullback (pullback.snd c J.toBase) (pts (Pic0.mk Dv)).left).TwoAffineOpenCover,
            Nontrivial (𝒲.sectionsOf (fibreAt c J.toBase (pts (Pic0.mk Dv)).left)
              (fibreModule c J.toBase (pts (Pic0.mk Dv)).left
                (h.poincare.L ⊗ sectionTwist c ε J.toBase d))).H0) ↔
          0 < ell ((Dv : Divisor k F) + Finsupp.single (M.pointEquivPlace ε') (d : ℤ)) := by sorry
