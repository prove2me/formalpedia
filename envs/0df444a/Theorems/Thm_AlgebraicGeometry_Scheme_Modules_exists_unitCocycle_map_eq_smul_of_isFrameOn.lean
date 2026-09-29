-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn
-- name    : AlgebraicGeometry.Scheme.Modules.exists_unitCocycle_map_eq_smul_of_isFrameOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/6f660384-6d9a-5eb9-9264-d80424421f5e
-- title:
--   Ratio cocycle of a family of frames
-- statement:
--   Let $X$ be a scheme, $\iota$ a type, $U : \iota \to$ Opens$(X)$ a family of open subsets of $X$, and $M$ an $\mathcal{O}_X$-module (an object of `X.Modules`). Suppose given sections $e_i \in \Gamma(M, U_i)$ for every $i$, each of which is a frame on its own open set in the sense of `IsFrameOn`: for every open $W$ with $W \le U_i$, the map $\Gamma(X, W) \to \Gamma(M, W)$, $g \mapsto g \cdot (e_i|_W)$, is bijective. The conclusion asserts the existence of a `UnitCocycle` $c$ for the family $U$ — that is, sections $c.u_{ij} \in \Gamma(X, U_i \sqcap U_j)$ of the structure sheaf on the pairwise intersections, with $c.u_{ii} = 1$ and with $c.u_{ij} \cdot c.u_{jk} = c.u_{ik}$ after restriction of all three factors to $U_i \sqcap U_j \sqcap U_k$ (the structure imposes no separate invertibility field) — such that for all $i, j$ the restriction of $e_j$ to $U_i \sqcap U_j$ equals $c.u_{ij}$ times the restriction of $e_i$ to $U_i \sqcap U_j$. No hypothesis is made that the $U_i$ cover $X$.
--
--   This is the passage from a family of local frames of a module to its transition (ratio) cocycle, in the form used to present a module framed on a family of opens as glued from a cocycle of units. It is cited in the treatment of invertible modules on schemes: in the comparison of an invertible module with the unit object over an open immersion, in the construction of locally trivial modules from pairwise trivialisations, and in the construction of the norm of an invertible module along a finite morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_unitCocycle_map_eq_smul_of_isFrameOn
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
    {M : X.Modules} (e : ∀ i, Γ(M, U i)) (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (U i)) :
    ∃ c : Scheme.Modules.UnitCocycle U, ∀ i j,
      M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
        c.u i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i) := by sorry
