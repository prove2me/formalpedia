-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_finrank_H1_tensorPow_add_two_le_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.isAlgEquivZero_of_finrank_H1_tensorPow_add_two_le_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/b1b224ef-8373-59c8-8157-9b36c1bb45ed
-- title:
--   h¹-test for algebraic equivalence to zero on two glued curves
-- statement:
--   Let $k$ be an algebraically closed field, let $x : X \to \operatorname{Spec} k$ be a proper morphism with $X$ reduced, and let $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be morphisms $C_1 \to X$, $C_2 \to X$ over $\operatorname{Spec} k$ (that is, pairs consisting of a morphism and a proof that composing with $x$ gives $c_\nu$) which are closed immersions, such that every point of $X$ lies in the image of $i_1$ or of $i_2$, and such that the scheme $C_1 \times_X C_2$ is reduced; let $s$ be a natural number equal to the cardinality of the underlying type of $C_1 \times_X C_2$, with $s > 0$. Let $L$ be an object of $X.\mathrm{Modules}$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ over which the restriction of $L$ along $U \hookrightarrow X$ is isomorphic to the unit module. Let $K$ be a natural number and let $\mathcal{W}$ be a cover of $X$ by two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \cap U_1$ affine. Assume that the first Čech cohomology of $\mathcal{W}$ with coefficients in $L^{\otimes K}$ — the quotient of $\Gamma(L^{\otimes K}, U_0 \cap U_1)$ by the image of $(m_0,m_1) \mapsto -\,\mathrm{res}\,m_0 + \mathrm{res}\,m_1$, viewed as a $k$-vector space through $x$, with $L^{\otimes K}$ the $K$-fold tensor power built from the unit module by repeated tensoring with $L$ — satisfies $\dim_k H^1 + 2 \le K$, and that the same inequality holds for $(L^{\vee})^{\otimes K}$, where $L^{\vee}$ is the internal hom from $L$ to the unit module. The conclusion is `IsAlgEquivZero x L`: there exist a scheme $T'$ with a morphism $h : T' \to \operatorname{Spec} k$ that is locally of finite type and geometrically integral, an invertible module $M$ on $X \times_{\operatorname{Spec} k} T'$, and two sections $t_0, t_1$ of $h$ over $\operatorname{Spec} k$, such that the pullback of $M$ along the base change of $x$ by $t_0$ is isomorphic to the unit module on $X \times_{\operatorname{Spec} k} \operatorname{Spec} k$, and the pullback of $M$ along the base change of $x$ by $t_1$ is isomorphic to the pullback of $L$ along the first projection of that fibre product.
--
--   This is one implication of the $h^1$-test characterising the line bundles in $\operatorname{Pic}^0$ of a curve obtained by gluing two smooth proper curves along a non-empty reduced finite intersection: smallness of the Čech $h^1$ of the $K$-th powers of $L$ and of its dual forces $L$ to be algebraically equivalent to zero, the algebraic equivalence being witnessed by a bundle on a family over a geometrically integral base with two specified fibres. It feeds the construction of an open locus of the base over which the fibres of a family of such degenerations satisfy the algebraic-equivalence condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_finrank_H1_tensorPow_add_two_le_of_twoGluedSmoothCurves.lean

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

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.isAlgEquivZero_of_finrank_H1_tensorPow_add_two_le_of_twoGluedSmoothCurves
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (K : ℕ) (𝒲 : X.TwoAffineOpenCover)
    (hpos : Module.finrank k (𝒲.sectionsOf x (L.tensorPow K)).H1 + 2 ≤ K)
    (hneg : Module.finrank k (𝒲.sectionsOf x ((Scheme.Modules.dual L).tensorPow K)).H1 + 2 ≤ K) :
    IsAlgEquivZero x L := by sorry
