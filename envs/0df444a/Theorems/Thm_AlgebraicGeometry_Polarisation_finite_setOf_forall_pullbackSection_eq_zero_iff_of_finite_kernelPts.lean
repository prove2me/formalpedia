-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_finite_setOf_forall_pullbackSection_eq_zero_iff_of_finite_kernelPts
-- name    : AlgebraicGeometry.Polarisation.finite_setOf_forall_pullbackSection_eq_zero_iff_of_finite_kernelPts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/4a19ac36-b925-5801-a51f-c10d2075559a
-- title:
--   Finite stabiliser of the zero locus of a section
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, equipped with a `RelativeGroupLaw` $L$ for $f$: functorial group operations on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections of $f$ above each $t : T \to \operatorname{Spec} k$, satisfying associativity, unit and inverse laws, with the multiplication natural in $T$. Assume further the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits some relative group law. Let $\mathcal M$ be a sheaf of modules on $A$ that is invertible in the sense that each point of $A$ has an open neighbourhood $U$ over which the pullback of $\mathcal M$ along $U \hookrightarrow A$ is isomorphic to the unit module sheaf, and assume that $\operatorname{kernelPts} f\, L\, \mathcal M$ is finite, i.e. only finitely many $k$-points $x$ of $A$ lie in the stabiliser of $\mathcal M$, meaning that the pullback of $\mathcal M$ along right translation by $x$ and the pullback of $\mathcal M$ along the first projection are locally isomorphic over the second projection. Let $\theta : \mathbf 1 \to \mathcal M$ be a non-zero global section of $\mathcal M$. Then, reading $A$ over $\operatorname{Spec} k$ as the group object in $\mathrm{Over}(\operatorname{Spec} k)$ determined by $L$, the set of $k$-points $x : \mathrm{Over.mk}(\mathbf 1_{\operatorname{Spec} k}) \to \mathrm{Over.mk}(f)$ such that for every $k$-point $z$ the pullback of $\theta$ along $z$ vanishes if and only if the pullback of $\theta$ along $z \cdot x$ vanishes is finite. Here the pullback of $\theta$ along a morphism is the inverse of the canonical isomorphism identifying the pullback of the unit with the unit, followed by the pullback of $\theta$.
--
--   This is the finiteness half of Mumford's comparison $H(D) \subseteq K(\mathcal O(D))$ for an abelian variety, in the form appropriate to the support of the zero locus: the set-theoretic stabiliser on $k$-points of the vanishing locus of a non-zero section of $\mathcal M$ is contained, up to finiteness, in the finite stabiliser group of $\mathcal M$ itself. It feeds the construction of a finite set of sections used for the projective embedding of the Jacobian, being cited by `finiteBySections_of_iso_tensorPow_three_of_finite_kernelPts_of_finrank_pos`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_finite_setOf_forall_pullbackSection_eq_zero_iff_of_finite_kernelPts.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.Polarisation.finite_setOf_forall_pullbackSection_eq_zero_iff_of_finite_kernelPts
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (hK : (kernelPts f L 𝓜).Finite)
    (θ : 𝟙_ A.Modules ⟶ 𝓜) (hθ : θ ≠ 0) :
    letI : GrpObj (Over.mk f) := L.grpObjOverMk
    Set.Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f |
        ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f,
          Scheme.Modules.pullbackSection z.left θ = 0 ↔ Scheme.Modules.pullbackSection (z * x).left θ = 0} := by sorry
