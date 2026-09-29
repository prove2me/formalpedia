-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isUnit_smul_eq
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isUnit_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/f41256bd-c446-53d4-8735-9f106b642687
-- title:
--   Two frames differ by a unit on a common open
-- statement:
--   Let $X$ be a scheme, let $M$ be an object of `X.Modules`, let $U$ be an open of $X$ and let $s, s'$ be sections of $M$ over $U$. Let $V$ be a further open, and suppose that both $s$ and $s'$ satisfy `Scheme.Modules.IsFrameOn` with respect to $V$, that is: for every open $W$ with $W \le U$ and $W \le V$, the map $\Gamma(X, W) \to \Gamma(M, W)$ sending $g$ to $g$ times the restriction of the section to $W$ is bijective (this for $s$, and likewise for $s'$). Let $W$ be an open with $W \le U$ and $W \le V$. Then there exists $u \in \Gamma(X, W)$ which is a unit of the ring $\Gamma(X, W)$ and satisfies $u \cdot s|_W = s'|_W$, the restrictions being taken along the map of $M$ induced by the inclusion $W \le U$. No uniqueness of $u$ is asserted, although it follows from the injectivity contained in the hypothesis on $s$.
--
--   This is the statement that two local frames (trivialisations) of a sheaf of modules over a common open differ by the multiplication by an invertible function, the classical transition function between trivialisations of an invertible sheaf. It is used in the comparison of constructions made from a chosen frame, for instance in producing isomorphisms with the unit object from frames and in the results on `IsFrameOn` that follow it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isUnit_smul_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isUnit_smul_eq
    {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {s s' : Γ(M, U)} {V : X.Opens}
    (hs : Scheme.Modules.IsFrameOn s V) (hs' : Scheme.Modules.IsFrameOn s' V)
    {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) :
    ∃ u : Γ(X, W), IsUnit u ∧
      u • M.presheaf.map (homOfLE hWU).op s = M.presheaf.map (homOfLE hWU).op s' := by sorry
