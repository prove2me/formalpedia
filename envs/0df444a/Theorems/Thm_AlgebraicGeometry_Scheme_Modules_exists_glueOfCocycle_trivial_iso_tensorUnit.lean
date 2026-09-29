-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_trivial_iso_tensorUnit
-- name    : AlgebraicGeometry.Scheme.Modules.exists_glueOfCocycle_trivial_iso_tensorUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/11c9afb5-24ca-5ca0-aedc-2421aae415e3
-- title:
--   The trivial cocycle glues to mathcal O_X
-- statement:
--   Let $X$ be a scheme, $\iota$ a type and $U : \iota \to X.\mathrm{Opens}$ a family of open subsets of $X$ with $\bigsqcup_i U_i = \top$, i.e. an open cover. Consider the unit cocycle `Scheme.Modules.UnitCocycle.trivial U`, whose transition data is $u_{ij} = 1 \in \Gamma(X, U_i \sqcap U_j)$ for all $i, j$ (reflexivity and the cocycle identity holding trivially), and the sheaf of $\mathcal O_X$-modules `Scheme.Modules.glueOfCocycle` obtained from it by gluing, whose sections over an open $T$ are the families $(x_i)_{i}$ with $x_i \in \Gamma(X, T \sqcap U_i)$ satisfying $x_i = u_{ij}\,x_j$ after restriction to $T \sqcap U_i \sqcap U_j$. The assertion is that there exists an isomorphism $\varphi$ in $X.\mathrm{Modules}$ from this glued module to the monoidal unit $\mathbb 1_{X.\mathrm{Modules}}$, that is to $\mathcal O_X$ viewed as a module over itself, such that for every index $i$ the map $\varphi$ on sections over $U_i$ sends the canonical frame `Scheme.Modules.glueFrame` of the trivial cocycle at $i$ — the family $k \mapsto u_{ki}$ restricted from $U_k \sqcap U_i$ to $U_i \sqcap U_k$, so here the constant family $1$ — to `Scheme.Modules.unitSection (U i)`, namely $1 \in \Gamma(X, U_i)$.
--
--   This identifies the module glued from the trivial transition data with the structure sheaf, normalised so that the canonical local frames correspond to the unit sections; it is the base case of the dictionary between invertible modules and unit cocycles on a cover. It is used in the construction of trivialisations of invertible modules over open immersions into spectra of unique factorisation domains, and in the norm-and-pullback comparison for finite morphisms to integrally closed schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_trivial_iso_tensorUnit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_glueOfCocycle_trivial_iso_tensorUnit
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) :
    ∃ φ : Scheme.Modules.glueOfCocycle (Scheme.Modules.UnitCocycle.trivial U) ≅ 𝟙_ X.Modules,
      ∀ i, φ.hom.app (U i) (Scheme.Modules.glueFrame (Scheme.Modules.UnitCocycle.trivial U) i) =
        Scheme.Modules.unitSection (U i) := by sorry
