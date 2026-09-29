-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle
-- name    : AlgebraicGeometry.Scheme.Modules.isInvertible_glueOfCocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/af35a763-0af0-5725-9e18-b2d1d8b79a29
-- title:
--   Modules glued from a unit cocycle are invertible
-- statement:
--   Let $X$ be a scheme, $\iota$ a type, and $U : \iota \to X.\mathrm{Opens}$ a family of open subsets of $X$ whose supremum is $\top$, i.e. the $U_i$ cover $X$. Let $c$ be a `Scheme.Modules.UnitCocycle` for this family: a family of sections $u_{ij} \in \Gamma(X, U_i \sqcap U_j)$ with $u_{ii} = 1$ for all $i$, and satisfying the multiplicative cocycle identity on triple intersections, namely that the restrictions of $u_{ij}$ and $u_{jk}$ to $U_i \sqcap U_j \sqcap U_k$ have product equal to the restriction of $u_{ik}$. The theorem asserts that the sheaf of $\mathcal{O}_X$-modules `Scheme.Modules.glueOfCocycle c`, obtained by gluing along $c$ (the presheaf of modules `preGlueMod c` together with its sheaf property), is invertible in the sense of `Scheme.Modules.IsInvertible`: for every point $x$ of $X$ there exists an open $U \subseteq X$ with $x \in U$ such that the pullback of the glued module along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module $\mathcal{O}_U$ on $U$, i.e. the glued module is locally free of rank one in this explicit trivialising sense.
--
--   This is the statement that the $\mathcal{O}_X$-module obtained from a multiplicative $1$-cocycle of units on an open cover is a line bundle, the module-theoretic half of the dictionary between $H^1$ of the units sheaf and invertible modules. It is used downstream when an invertible module trivialised on a cover is recognised as the glue of its transition cocycle, for instance in semilocal triviality statements and in the construction of norms of line bundles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.isInvertible_glueOfCocycle
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (c : Scheme.Modules.UnitCocycle U) :
    Scheme.Modules.IsInvertible (Scheme.Modules.glueOfCocycle c) := by sorry
