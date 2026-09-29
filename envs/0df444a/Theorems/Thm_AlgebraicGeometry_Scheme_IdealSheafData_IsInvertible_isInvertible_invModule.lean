-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isInvertible_invModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/401125ef-bc17-5199-8e2c-4ef3664bf48d
-- title:
--   Invertibility of the dual of an invertible ideal sheaf
-- statement:
--   Let $X$ be a scheme and let $I$ be an ideal sheaf datum on $X$. Assume $I$ satisfies `IsInvertible`: for every point $x$ of $X$ there are an affine open $U$ of $X$ and a section $f \in \Gamma(X, U)$ with $x$ lying in the basic open $X.\mathrm{basicOpen}\, f$, together with an element $g$ of the non-zero-divisors of $\Gamma(X, X.\mathrm{affineBasicOpen}\, f)$ such that the ideal cut out by $I$ on $X.\mathrm{affineBasicOpen}\, f$ equals the span of $\{g\}$. The conclusion is that the sheaf of modules `I.invModule` is invertible in the sense of `Scheme.Modules.IsInvertible`, i.e. every point of $X$ has an open neighbourhood $U$ for which the pullback of `I.invModule` along the inclusion $U \hookrightarrow X$ is isomorphic to the unit object, the structure sheaf of $U$ viewed as a sheaf of modules over itself. Here `I.invModule` is the dual $\mathcal{H}om(I.\mathrm{module}, \mathcal O_X)$, namely the internal hom object $(\mathrm{ihom}\, I.\mathrm{module}).\mathrm{obj}\,(\mathbf 1)$ in the monoidal category of sheaves of modules on $X$, and `I.module` is the kernel of the canonical map from the unit to the pushforward of the unit along the closed immersion $I.\mathrm{subschemeι}$ determined by $I$.
--
--   This is the standard fact that for an invertible sheaf of ideals $\mathcal I = \mathcal O_X(-Z)$ the dual $\mathcal O_X(Z) = \mathcal{H}om(\mathcal I, \mathcal O_X)$ is a line bundle. It is used throughout the treatment of relative effective Cartier divisors and the Picard functor on curves, where the line bundle attached to a divisor is produced as such a dual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule.lean

import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isInvertible_invModule
    {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) :
    Scheme.Modules.IsInvertible I.invModule := by sorry
