-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.of_iSup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/132a7b06-d871-5f30-91dc-7b3859e0bdc9
-- title:
--   Frames glue: IsFrameOn is stable under suprema of opens
-- statement:
--   Let $X$ be a scheme, $M$ an object of `X.Modules` (a sheaf of $\mathcal{O}_X$-modules on $X$), $U$ an open of $X$, $\iota$ an arbitrary index type and $s \in \Gamma(M, U)$ a section of $M$ over $U$. Here `Scheme.Modules.IsFrameOn s V`, for an open $V$, means: for every open $W$ with $W \le U$ and $W \le V$, the map $\Gamma(X, W) \to \Gamma(M, W)$, $g \mapsto g \cdot (s|_W)$, given by multiplication of the restriction of $s$ along $W \le U$ by sections of the structure sheaf, is bijective. The theorem asserts: given a family of opens $V : \iota \to$ `X.Opens` such that $s$ is a frame on each $V_i$ in this sense, $s$ is a frame on the supremum $\bigsqcup_i V_i$, i.e. for every open $W \le U$ contained in $\bigcup_i V_i$ multiplication by $s|_W$ is a bijection $\Gamma(X, W) \to \Gamma(M, W)$. No nonemptiness of $\iota$ is assumed, and the index type lives in an arbitrary universe.
--
--   This records that being a trivialising (nowhere-vanishing generating) section of a sheaf of modules over an open is a local condition on that open: local frames on a family of opens assemble to a frame on their union. It is used to produce frames and trivialisations on larger opens from local ones, for instance in the construction of relative Picard data and in the comparisons of modules with the tensor unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.of_iSup
    {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {ι : Type v} {s : Γ(M, U)}
    (V : ι → X.Opens) (h : ∀ i, Scheme.Modules.IsFrameOn s (V i)) :
    Scheme.Modules.IsFrameOn s (⨆ i, V i) := by sorry
