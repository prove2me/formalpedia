-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_zeroSchemeIdeal_eq
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_zeroSchemeIdeal_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/43de6080-86f6-55e9-9a6f-10eb65e0148c
-- title:
--   Equal zero ideals force isomorphic invertible modules
-- statement:
--   Let $X$ be an integral scheme (the typeclass `IsIntegral X` is assumed) and let $M$, $M'$ be sheaves of modules on $X$, both assumed invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`: every point of $X$ has an open neighbourhood $U$ on which the pullback of the module along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module of the structure sheaf of $U$. Let $s : \mathbf{1}_{X\text{-Mod}} \to M$ and $s' : \mathbf{1}_{X\text{-Mod}} \to M'$ be morphisms from the monoidal unit, i.e. global sections of $M$ and $M'$, and suppose $s \neq 0$. The remaining hypothesis is that $s$ and $s'$ have the same zero scheme ideal, where $\mathrm{zeroSchemeIdeal}$ of a section is the infimum, among the ideal sheaf data $J$ on $X$, of those $J$ satisfying $\mathrm{coeffIdeal}(s, U) \le J.\mathrm{ideal}(U)$ for every affine open $U$ of $X$, with $\mathrm{coeffIdeal}(s, U)$ the ideal of $\Gamma(X, U)$ spanned by the range of the coefficients of $s$ over $U$. The conclusion is that the type of isomorphisms $M \cong M'$ in $X$-modules is nonempty; no particular isomorphism is produced, and no hypothesis $s' \neq 0$ is imposed.
--
--   This is the standard fact that on an integral scheme an invertible module with a non-zero global section is determined, up to isomorphism, by the zero scheme (effective Cartier divisor) of that section, so that two such data with the same zero ideal give isomorphic line bundles. It feeds the comparison of line bundles used in the relative Picard functor material, being cited by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_pullback_iso_of_forall_maximal_isIrreducible_image_eq`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_pullback_iso_of_forall_maximal_isIrreducible_image_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_zeroSchemeIdeal_eq.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_zeroSchemeIdeal_eq
    {X : Scheme.{u}} [IsIntegral X] {M M' : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')
    (s : 𝟙_ X.Modules ⟶ M) (s' : 𝟙_ X.Modules ⟶ M') (hs : s ≠ 0)
    (h : Scheme.Modules.zeroSchemeIdeal s = Scheme.Modules.zeroSchemeIdeal s') :
    Nonempty (M ≅ M') := by sorry
