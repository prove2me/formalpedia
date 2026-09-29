-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/05e20527-542c-5e63-8441-f5dd4998d94e
-- title:
--   Trivialisation over U yields a frame on U
-- statement:
--   Let $X$ be a scheme, let $M$ be a sheaf of $\mathcal{O}_X$-modules (an object of `X.Modules`), and let $U$ be an open of $X$. Suppose given an isomorphism $eU$, in the category of sheaves of modules on the open subscheme $U$, between the pullback of $M$ along the open immersion $U.\iota : U \to X$ and the unit object `SheafOfModules.unit` of the structure sheaf of $U$ viewed as a module over itself. The conclusion asserts the existence of a section $s \in \Gamma(M, U)$ which is a frame of $M$ on $U$ in the sense of the predicate `Scheme.Modules.IsFrameOn`: for every open $W$ of $X$ together with proofs that $W \le U$ and $W \le U$, the map from $\Gamma(X, W)$ to $\Gamma(M, W)$ sending $g$ to $g$ acting by scalar multiplication on the restriction of $s$ to $W$ (the image of $s$ under the presheaf map of $M$ along the inclusion $W \le U$) is bijective. Thus a trivialisation of $M$ over $U$ produces a global generator of $M$ over $U$ which generates freely on each smaller open.
--
--   This is the standard statement that a sheaf of modules trivialised over an open subscheme admits a nowhere-vanishing free generator there, the converse direction of the equivalence between 'trivial over $U$' and 'framed on $U$'. It is used in the treatment of invertible sheaves of modules, in particular by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.bijective_lift_tensorSectionsBilin_monoidalV2`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.bijective_lift_tensorSectionsBilin_monoidalV2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit_monoidalV2
    {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (eU : (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    ∃ s : Γ(M, U), Scheme.Modules.IsFrameOn s U := by sorry
