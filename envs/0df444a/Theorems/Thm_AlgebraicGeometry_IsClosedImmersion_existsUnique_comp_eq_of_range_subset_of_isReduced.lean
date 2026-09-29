-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced
-- name    : AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/4566cfd7-8a76-55dc-a444-589e66df2bb7
-- title:
--   Factoring through a closed immersion over a reduced scheme
-- statement:
--   Let $X$, $Y$, $T$ be schemes (in a fixed universe), let $i \colon Y \to X$ be a morphism of schemes that is a closed immersion, and let $f \colon T \to X$ be a morphism whose source $T$ is a reduced scheme. Assume that the image of the underlying continuous map of $f$ is contained in the image of the underlying continuous map of $i$, i.e. $\operatorname{range}(|f|) \subseteq \operatorname{range}(|i|)$ as subsets of the topological space $|X|$. Then there is exactly one morphism of schemes $g \colon T \to Y$ with $g$ followed by $i$ equal to $f$; that is, the statement asserts existence and uniqueness together, in the form of a `∃!` over morphisms $T \to Y$ subject to the factorisation equation $g \circ i$ (in diagrammatic order, `g ≫ i`) $= f$.
--
--   This is the standard factorisation criterion for maps from a reduced scheme into a closed subscheme: set-theoretic containment of images suffices for a (necessarily unique) scheme-theoretic factorisation. It is used throughout the development whenever a point or section of $X$ whose support lies in a closed subscheme $Y$ must be recognised as a point or section of $Y$, for instance in the construction of closed immersions into pullbacks along irreducible components and in the flat-descent form of the same factorisation statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced
    {X Y T : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (f : T ⟶ X) [IsReduced T]
    (H : Set.range f.base ⊆ Set.range i.base) :
    ∃! g : T ⟶ Y, g ≫ i = f := by sorry
