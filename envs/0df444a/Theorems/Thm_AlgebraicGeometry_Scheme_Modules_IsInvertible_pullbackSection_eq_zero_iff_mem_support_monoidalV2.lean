-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/62e6142d-d33e-56b8-9493-e863aae0291a
-- title:
--   Field-valued points where a section of an invertible module vanishes
-- statement:
--   Let $k$ be a field, $X$ a scheme, and $M$ an $\mathcal O_X$-module in the sense of `X.Modules`, assumed invertible in the project's sense: every point of $X$ has an open neighbourhood $U$ such that the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit object, the structure sheaf of $U$ viewed as a sheaf of modules over itself. Let $s \colon \mathbf 1_{X.\mathrm{Modules}} \to M$ be a global section, i.e. a morphism from the unit object, and let $z \colon \operatorname{Spec} k \to X$ be a $k$-valued point. The assertion is that the pulled-back section `Scheme.Modules.pullbackSection z s`, namely the inverse of the canonical isomorphism identifying $z^{*}\mathbf 1$ with the unit object on $\operatorname{Spec} k$ followed by $z^{*}s$, is the zero morphism if and only if the image under the underlying map of $z$ of the closed point of $\operatorname{Spec} k$ (its unique point) lies in the support of the ideal sheaf data `Scheme.Modules.zeroSchemeIdeal s`, defined as the infimum of all ideal sheaf data $J$ on $X$ with $\mathrm{coeffIdeal}(s, U) \le J.\mathrm{ideal}\,U$ for every affine open $U$, where $\mathrm{coeffIdeal}(s,U) \subseteq \Gamma(X,U)$ is the ideal spanned by the coefficients of $s$ over $U$.
--
--   This is the pointwise vanishing criterion for a section of a line bundle: the value of $s$ at a field-valued point is zero exactly when that point lies on the zero scheme of $s$, cut out by the ideal generated locally by the coefficient of $s$ with respect to a trivialisation. It is used in the study of the relative Picard functor and of polarisations, where stabiliser conditions are tested by pulling sections back to points with values in fields and in dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support_monoidalV2.lean

import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support_monoidalV2
    {k : Type u} [Field k] {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) (z : Spec (CommRingCat.of k) ⟶ X) :
    Scheme.Modules.pullbackSection z s = 0 ↔
      z.base (IsLocalRing.closedPoint k) ∈ (Scheme.Modules.zeroSchemeIdeal s).support := by sorry
