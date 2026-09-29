-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_finrank_H1_le_finrank_H1_unit_add_one_of_isAlgEquivZero_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.finrank_H1_le_finrank_H1_unit_add_one_of_isAlgEquivZero_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/4f1a09c2-b17f-53f0-b03f-29750c298098
-- title:
--   Čech h¹ bound for algebraically trivial bundles on glued curves
-- statement:
--   Let $k$ be an algebraically closed field, and let $x \colon X \to \operatorname{Spec} k$ be proper with $X$ reduced. Let $c_1 \colon C_1 \to \operatorname{Spec} k$ and $c_2 \colon C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $i_1, i_2$ be morphisms $C_\nu \to X$ over $\operatorname{Spec} k$ (so $i_\nu$ followed by $x$ is $c_\nu$) which are closed immersions, with the hypothesis that every point of $X$ lies in the image of $i_1$ or of $i_2$. Let $L$ be a sheaf of modules on $X$ that is invertible, in the sense that each point of $X$ has an open neighbourhood $U$ on which the pullback of $L$ along $U \hookrightarrow X$ is isomorphic to the unit module of $U$, and assume $L$ satisfies `IsAlgEquivZero` for $x$: there are a scheme $T'$ with a locally of finite type, geometrically integral morphism $h \colon T' \to \operatorname{Spec} k$, an invertible module $M$ on $X \times_k T'$, and two sections $t_0, t_1$ of $h$ over $\operatorname{Spec} k$, such that the pullback of $M$ along the base change of $t_0$ is isomorphic to the unit module on $X \times_k \operatorname{Spec} k$, while its pullback along the base change of $t_1$ is isomorphic to the pullback of $L$ along the first projection. Let $\mathcal{W}$ consist of two affine opens $U_0, U_1$ of $X$ with $U_0 \cup U_1 = X$ and $U_0 \cap U_1$ affine, and assume that the degree-zero cohomology of the two-term Čech complex of $\mathcal{W}$ with coefficients in the unit module, namely the kernel of $(s_0,s_1) \mapsto s_1|_{U_0 \cap U_1} - s_0|_{U_0 \cap U_1}$ on $\Gamma(U_0) \times \Gamma(U_1)$, has $k$-dimension $1$. Then the degree-one Čech cohomology of $\mathcal{W}$ with coefficients in $L$, that is the quotient of $\Gamma(L, U_0 \cap U_1)$ by the image of that differential, satisfies $\dim_k \check H^1(\mathcal{W}, L) \le \dim_k \check H^1(\mathcal{W}, \mathcal{O}_X) + 1$.
--
--   This is the forward half of the $h^1$-criterion used to cut out the algebraically trivial part of the Picard group of a curve with two smooth proper components glued along a finite set, no transversality at the crossings being required. It is used in the proof that, for a family of such two-component degenerations, the locus of fibres on which a given line bundle is algebraically equivalent to zero is open in the smooth locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_finrank_H1_le_finrank_H1_unit_add_one_of_isAlgEquivZero_of_twoGluedSmoothCurves.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.finrank_H1_le_finrank_H1_unit_add_one_of_isAlgEquivZero_of_twoGluedSmoothCurves
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero x L)
    (𝒲 : X.TwoAffineOpenCover)
    (hH0 : Module.finrank k (𝒲.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 = 1) :
    Module.finrank k (𝒲.sectionsOf x L).H1 ≤
      Module.finrank k (𝒲.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 + 1 := by sorry
