-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_stalkMap_of_isClosedImmersion_of_not_mem_range
-- name    : AlgebraicGeometry.isIso_stalkMap_of_isClosedImmersion_of_not_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/9e30c392-82c5-539a-b76e-801f7bf41513
-- title:
--   Stalk isomorphism off the complementary closed component
-- statement:
--   Let $Z$, $M_1$, $M_2$ be schemes (in a fixed universe) with $Z$ reduced, and let $i_1 \colon M_1 \to Z$ and $i_2 \colon M_2 \to Z$ be closed immersions. Assume that the two images cover $Z$ topologically, i.e. every point $z$ of the underlying space of $Z$ lies in the range of the continuous map underlying $i_1$ or in the range of the continuous map underlying $i_2$. Let $y$ be a point of $M_1$ whose image $i_1(y)$ does not lie in the range of the map underlying $i_2$. Then the induced map on stalks $\mathcal{O}_{Z,\,i_1(y)} \to \mathcal{O}_{M_1,\,y}$, written `i₁.stalkMap y`, is an isomorphism of (commutative) rings, in the sense that it is an isomorphism in the relevant category of locally ringed-space stalks, i.e. `IsIso` holds for it. Note that the covering hypothesis is on the topological images only, and that no condition relating the scheme structures of $M_1$ and $M_2$ beyond their being closed subschemes of $Z$ is imposed.
--
--   This is the standard statement that, on the locus of a reduced scheme covered by two closed subschemes where only one of them passes, that subscheme agrees with the ambient scheme locally: away from the second component the first closed immersion is locally an isomorphism. It is used in the analysis of the local rings of the Deligne–Rapoport model of a modular curve at $p$, where the special fibre is covered by two closed components and one works near a point lying on only one of them; three results about stalks, integral closedness, Krull dimension and orders of residues on that model cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_stalkMap_of_isClosedImmersion_of_not_mem_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_stalkMap_of_isClosedImmersion_of_not_mem_range
    {Z M₁ M₂ : Scheme.{u}} [IsReduced Z]
    (i₁ : M₁ ⟶ Z) (i₂ : M₂ ⟶ Z) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : ∀ z : Z, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (y : M₁) (hy : i₁.base y ∉ Set.range i₂.base) :
    IsIso (i₁.stalkMap y) := by sorry
