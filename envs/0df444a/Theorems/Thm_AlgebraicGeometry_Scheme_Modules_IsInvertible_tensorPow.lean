-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.tensorPow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/1b4beb86-4e42-5b81-81de-f91fd76e3755
-- title:
--   Tensor powers of an invertible sheaf of modules are invertible
-- statement:
--   Let $X$ be a scheme and let $L$ be an object of $X.\text{Modules}$, the category of sheaves of modules over the structure sheaf of $X$, with its monoidal structure. Assume $L$ satisfies the predicate `Scheme.Modules.IsInvertible`, i.e. for every point $x$ of $X$ there is an open subscheme $U$ of $X$ with $x \in U$ such that the pullback of $L$ along the open immersion $U.\iota \colon U \to X$ is isomorphic, as a sheaf of modules on $U$, to the unit object `SheafOfModules.unit` of the sheaf of rings of $U$ (the isomorphism is asserted only as a nonempty type, the whole condition being a proposition). Then for every natural number $n$ the $n$-th tensor power $L.\text{tensorPow}\,n$ is again invertible in this sense. Here `tensorPow` is defined by recursion on $n$: the value at $0$ is the monoidal unit $\mathbb{1}_{X.\text{Modules}}$, and the value at $n+1$ is $(L.\text{tensorPow}\,n) \otimes L$.
--
--   This is the standard fact that the powers $\mathcal{L}^{\otimes n}$ of a line bundle on a scheme are again line bundles, with $\mathcal{L}^{\otimes 0} = \mathcal{O}_X$. It is used throughout the treatment of relative Picard functors and of ampleness-type statements, where assertions about some power of a bundle (global generation, finiteness of maps defined by sections, cohomological vanishing) presuppose that each power is invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.tensorPow {X : Scheme.{u}} {L : X.Modules}
    (hL : Scheme.Modules.IsInvertible L) (n : ℕ) : Scheme.Modules.IsInvertible (L.tensorPow n) := by sorry
