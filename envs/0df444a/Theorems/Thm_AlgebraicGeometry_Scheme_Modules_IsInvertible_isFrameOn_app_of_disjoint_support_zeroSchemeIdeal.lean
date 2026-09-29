-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/6310d2fe-068f-5aa4-aa6c-73b4cad17fb6
-- title:
--   Global section of an invertible module frames off its zero scheme
-- statement:
--   Let $X$ be a scheme and let $M$ be an $\mathcal O_X$-module on $X$ which is invertible in the sense of the predicate `Scheme.Modules.IsInvertible`: every point of $X$ has an open neighbourhood $U$ for which the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Let $s \colon \mathbf 1_{X\text{-Mod}} \to M$ be a morphism from the monoidal unit, i.e. a global section of $M$, and let $V$ be an open subset of $X$. Assume that $V$, as a subset of the underlying space of $X$, is disjoint from the support of `Scheme.Modules.zeroSchemeIdeal s`, the ideal-sheaf datum obtained as the infimum of all ideal-sheaf data $J$ with $\mathrm{coeffIdeal}(s, U) \le J(U)$ for every affine open $U$, where $\mathrm{coeffIdeal}(s, U)$ is the ideal of $\Gamma(X, U)$ spanned by the range of the coefficient function $\mathrm{coeff}\,s\,U$. The conclusion is that the element $\sigma = s_{\top}(1) \in \Gamma(M, \top)$, the image under $s$ on the whole of $X$ of the unit section $1$ of the unit module, is a frame on $V$: for every open $W \le \top$ with $W \le V$, the map $\Gamma(X, W) \to \Gamma(M, W)$ sending $g$ to $g \cdot (\sigma|_W)$ is bijective.
--
--   This is the standard statement that a global section of a line bundle trivialises it away from the support of its zero scheme, so that on such opens $M$ is free of rank one on the section; it is the bridge between the description of a section as a morphism from the unit together with its zero-scheme ideal and the frame predicate used for sections viewed as elements. It is invoked, among other places, in the computation of Euler characteristics of twists by pushforwards of the unit and in the local analysis of relative Picard groups at nodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (V : X.Opens) (hV : Disjoint (V : Set X) (Scheme.Modules.zeroSchemeIdeal s).support) :
    Scheme.Modules.IsFrameOn (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) V := by sorry
