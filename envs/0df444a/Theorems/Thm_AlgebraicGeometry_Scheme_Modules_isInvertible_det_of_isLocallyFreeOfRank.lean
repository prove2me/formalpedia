-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
-- name    : AlgebraicGeometry.Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/ec8fc81b-9e33-5518-85cd-c02f07983456
-- title:
--   Determinant of a locally free sheaf of rank n is invertible
-- statement:
--   Let $X$ be a scheme and let $M$ be a sheaf of modules over the structure sheaf of $X$ (an object of `X.Modules`), and let $n$ be a natural number. The hypothesis `hM` is that $M$ is locally free of rank $n$ in the following sense: for every point $x$ of $X$ there is an open subset $U$ of $X$ containing $x$ such that the pullback of $M$ along the open immersion $U \hookrightarrow X$ is isomorphic, as a sheaf of modules on $U$, to the free sheaf of modules on the index type $\mathrm{ULift}(\mathrm{Fin}\ n)$ (the isomorphism being asserted merely to exist, as a `Nonempty` of the type of isomorphisms). The conclusion is that $\det_n M$, defined as the value at $M$ of the $n$-th exterior power functor on `X.Modules` — namely: pass to the underlying presheaf of modules, form the $n$-th exterior power presheaf, and sheafify — is invertible in the corresponding local sense: for every point $x$ of $X$ there is an open $U$ containing $x$ with $x \in U$ such that the pullback of $\det_n M$ along $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$, i.e. to $\mathcal{O}_U$ regarded as a sheaf of modules over itself.
--
--   This is the standard statement that the determinant $\bigwedge^n \mathcal{E}$ of a locally free sheaf $\mathcal{E}$ of rank $n$ is a line bundle. It is used in the construction of the theta line bundle attached to a Picard bundle on a relative Jacobian, which in turn feeds the quasi-projectivity of the relative Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    (hM : Scheme.Modules.IsLocallyFreeOfRank n M) :
    Scheme.Modules.IsInvertible (Scheme.Modules.det n M) := by sorry
