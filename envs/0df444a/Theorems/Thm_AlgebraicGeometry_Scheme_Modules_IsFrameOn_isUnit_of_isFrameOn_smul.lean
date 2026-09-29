-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_isUnit_of_isFrameOn_smul
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.isUnit_of_isFrameOn_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/248c8df5-d999-5329-9374-6babb0a58e6d
-- title:
--   Ratio of two frames is a unit
-- statement:
--   Let $X$ be a scheme, $M$ an object of `X.Modules` (a presheaf of modules over $\mathcal{O}_X$), and let $U$, $V$, $W$ be open subsets of $X$. Let $s \in \Gamma(M,U)$ be a section, and assume `IsFrameOn s V`, that is: for every open $W'$ with $W' \le U$ and $W' \le V$, the map $\Gamma(X,W') \to \Gamma(M,W')$ sending $h$ to $h \cdot (s|_{W'})$ (restriction along the inclusion $W' \le U$) is bijective. Assume further $W \le U$ and $W \le V$, and let $g \in \Gamma(X,W)$ be a function such that the section $g \cdot (s|_W) \in \Gamma(M,W)$ satisfies `IsFrameOn (g • M.presheaf.map (homOfLE hWU).op s) W`, i.e. for every open $W'' \le W$ the map $\Gamma(X,W'') \to \Gamma(M,W'')$ sending $h$ to $h \cdot \bigl((g \cdot s|_W)|_{W''}\bigr)$ is bijective. The conclusion is that $g$ is a unit of the ring $\Gamma(X,W)$.
--
--   This is the statement that two frames (local generators with the freeness property encoded by `IsFrameOn`) differ by an invertible function: if a multiple $g \cdot s$ of a frame $s$ is again a frame, the multiplier $g$ is invertible. It is used in the construction of the canonical morphism to projective space, via [`AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_isCanonicalToProj`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_isCanonicalToProj).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_isUnit_of_isFrameOn_smul.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.isUnit_of_isFrameOn_smul
    {X : Scheme.{u}} {M : X.Modules} {U V W : X.Opens} (s : Γ(M, U))
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V) (hWU : W ≤ U) (hWV : W ≤ V) (g : Γ(X, W))
    (hg : AlgebraicGeometry.Scheme.Modules.IsFrameOn (g • M.presheaf.map (homOfLE hWU).op s) W) :
    IsUnit g := by sorry
