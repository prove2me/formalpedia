-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_of_isFrameOn_of_isFrameOn_of_sup_eq_top
-- name    : AlgebraicGeometry.Scheme.Modules.isInvertible_of_isFrameOn_of_isFrameOn_of_sup_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/c1946a86-0568-5b73-bd53-433b65279992
-- title:
--   Modules framed on two opens covering X are invertible
-- statement:
--   Let $X$ be a scheme, $M$ a sheaf of $\mathcal O_X$-modules (an object of `X.Modules`), and $U, V$ two open subsets of $X$. Let $a \in \Gamma(M, U)$ and $b \in \Gamma(M, V)$ be sections, and assume: $a$ satisfies `IsFrameOn a U`, i.e. for every open $W \le U$ the map $\Gamma(X, W) \to \Gamma(M, W)$, $g \mapsto g \cdot (a|_W)$, is bijective; $b$ satisfies `IsFrameOn b V`, i.e. for every open $W \le V$ the map $\Gamma(X, W) \to \Gamma(M, W)$, $g \mapsto g \cdot (b|_W)$, is bijective; and $U \sqcup V = \top$, so that $U$ and $V$ cover $X$. The conclusion is `Scheme.Modules.IsInvertible M`: every point $x$ of $X$ has an open neighbourhood $U'$ for which the pullback of $M$ along the inclusion $U' \hookrightarrow X$ is isomorphic, as a sheaf of modules over the structure sheaf of $U'$, to the unit object $\mathcal O_{U'}$. Note that the frame conditions are imposed on the full opens of definition ($V := U$ for $a$, $V := V$ for $b$ in the definition of `IsFrameOn`), i.e. each section freely generates $M$ over its own open.
--
--   This is the two-chart case of the local criterion for a module sheaf to be a line bundle: a module trivialised by a single free generator on each of two opens covering $X$ lies in $\mathrm{Pic}(X)$. It is used in the two-affine-chart description of line bundles on curves, in the constructions attached to the relative Picard functor for the modular curves $X_1(p)$ and the model at $p$ used there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_of_isFrameOn_of_isFrameOn_of_sup_eq_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isInvertible_of_isFrameOn_of_isFrameOn_of_sup_eq_top
    {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens}
    {a : Γ(M, U)} {b : Γ(M, V)}
    (ha : Scheme.Modules.IsFrameOn a U) (hb : Scheme.Modules.IsFrameOn b V) (hUV : U ⊔ V = ⊤) :
    Scheme.Modules.IsInvertible M := by sorry
