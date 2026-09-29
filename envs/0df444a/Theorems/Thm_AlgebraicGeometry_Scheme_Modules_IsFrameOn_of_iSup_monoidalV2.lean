-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.of_iSup_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/d0bb7633-0270-593b-aa27-d1d8319785a4
-- title:
--   Being a frame is local on the open: stability under suprema
-- statement:
--   Let $X$ be a scheme, $M$ an $\mathcal O_X$-module on $X$ (an object of `X.Modules`), $U$ an open of $X$ and $s \in \Gamma(M,U)$ a section of $M$ over $U$. Here the project predicate `IsFrameOn s V`, for an open $V$, asserts that for every open $W$ with $W \le U$ and $W \le V$ the map $\Gamma(X,W) \to \Gamma(M,W)$ sending a ring section $g$ to $g \cdot (s|_W)$, where $s|_W$ is the image of $s$ under the restriction $M.\mathrm{presheaf}$ applied to the inclusion $W \le U$, is bijective. Given an index type $\iota$ (in an arbitrary universe) and a family $V : \iota \to X.\mathrm{Opens}$ such that `IsFrameOn s (V i)` holds for every $i$, the conclusion is `IsFrameOn s (⨆ i, V i)`: for every open $W$ contained in $U$ and in the supremum $\bigcup_i V_i$, multiplication by $s|_W$ is a bijection $\Gamma(X,W) \to \Gamma(M,W)$.
--
--   This is the statement that the property of a section being a frame (in the sense of the displayed bijectivity condition, i.e. $s$ generating $M$ freely of rank one) is local on the open over which it is tested, so that it may be checked on the members of an open cover. It is used in the construction of canonical maps to projective space from section rings of graded $\mathcal O_X$-algebras, and in the criterion for a morphism defined by sections to be a closed immersion in the study of abelian schemes with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.of_iSup_monoidalV2
    {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {ι : Type v} {s : Γ(M, U)}
    (V : ι → X.Opens) (h : ∀ i, AlgebraicGeometry.Scheme.Modules.IsFrameOn s (V i)) :
    AlgebraicGeometry.Scheme.Modules.IsFrameOn s (⨆ i, V i) := by sorry
