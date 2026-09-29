-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.tensorPow_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/e68c3c47-ccde-5d5c-8e69-be634c71c16c
-- title:
--   Tensor powers of an invertible module are invertible
-- statement:
--   Let $X$ be a scheme (in a fixed universe) and let $L$ be an object of the category $X.\mathrm{Modules}$ of sheaves of modules over the structure sheaf of $X$. Assume $L$ satisfies the predicate `Scheme.Modules.IsInvertible`, that is: for every point $x \in X$ there is an open subscheme $U \subseteq X$ with $x \in U$ such that the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules $\mathcal{O}_U$ on $U$ (the isomorphism is required only to exist, the predicate being a proposition). Then for every natural number $n$ the $n$-th tensor power `L.tensorPow n`, defined by recursion as the monoidal unit $\mathbb{1}_{X.\mathrm{Modules}}$ for $n = 0$ and as `L.tensorPow n ⊗ L` for $n+1$ (tensor product taken in the monoidal structure on $X.\mathrm{Modules}$), is again invertible in the same sense: it is locally, in the Zariski topology on $X$, isomorphic to the structure sheaf after pullback to a suitable open neighbourhood of each point.
--
--   This is the standard fact that $\mathcal{L}^{\otimes n}$ is a line bundle whenever $\mathcal{L}$ is, in the form needed to feed tensor powers into statements about sections, ampleness, Serre vanishing and cohomology and base change. It is used throughout the development wherever a construction quantifies over the powers of a line bundle, for instance in the treatment of Hilbert functors and of section rings of graded algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.tensorPow_monoidalV2 {X : Scheme.{u}} {L : X.Modules}
    (hL : Scheme.Modules.IsInvertible L) (n : ℕ) : Scheme.Modules.IsInvertible (L.tensorPow n) := by sorry
