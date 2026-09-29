-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/25cc4718-4d4c-502f-8f62-34148a00c1e4
-- title:
--   Pullback of a section vanishes iff the point lies in the zero scheme
-- statement:
--   Let $k$ be a field, $X$ a scheme and $M$ a sheaf of modules on $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ for which the pullback of $M$ along the inclusion $U \hookrightarrow X$ admits an isomorphism to the unit sheaf of modules on $U$. Let $s : \mathbf{1} \to M$ be a morphism from the monoidal unit of $X$-modules, i.e. a global section of $M$, and let $z : \operatorname{Spec} k \to X$ be a $k$-valued point. Write $z^{*}s$ for `Scheme.Modules.pullbackSection z s`, the morphism $\mathbf{1} \to z^{*}M$ obtained from the canonical isomorphism identifying the pullback of the unit with the unit on $\operatorname{Spec} k$, followed by the pullback of $s$ along $z$. Let `Scheme.Modules.zeroSchemeIdeal s` be the ideal sheaf datum on $X$ defined as the infimum of all ideal sheaf data $J$ with $\operatorname{span}(\operatorname{range}(\mathrm{coeff}\, s\, U)) \le J(U)$ for every affine open $U$. The assertion is that $z^{*}s = 0$ if and only if the image under $z$ of the closed point of $\operatorname{Spec} k$ lies in the support of `Scheme.Modules.zeroSchemeIdeal s`.
--
--   This is the point-vanishing criterion for a global section of a line bundle: the value of $s$ at a field-valued point vanishes exactly when the point lies on the zero scheme of $s$. It is used to recognise sections which are nowhere zero, and hence trivialisations of line bundles, for instance in the comparison of rigidified line bundles on relative curves with the unit bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support.lean

import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support
    {k : Type u} [Field k] {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) (z : Spec (CommRingCat.of k) ⟶ X) :
    Scheme.Modules.pullbackSection z s = 0 ↔
      z.base (IsLocalRing.closedPoint k) ∈ (Scheme.Modules.zeroSchemeIdeal s).support := by sorry
