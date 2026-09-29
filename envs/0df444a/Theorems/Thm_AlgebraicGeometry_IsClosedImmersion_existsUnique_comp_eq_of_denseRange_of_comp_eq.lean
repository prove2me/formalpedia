-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_denseRange_of_comp_eq
-- name    : AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_denseRange_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/b9737f62-705c-52f3-93f0-b6bb34779036
-- title:
--   Factorisation through a closed subscheme over a reduced scheme
-- statement:
--   Let $W, X, Y, Z$ be schemes (in a fixed universe) with $X$ reduced, let $g : W \to X$ be a morphism whose underlying continuous map has dense range, let $\iota : Z \to Y$ be a closed immersion, let $\varphi : X \to Y$ be a morphism, and suppose given $\psi : W \to Z$ with $\psi$ followed by $\iota$ equal to $g$ followed by $\varphi$, i.e. $\iota \circ \psi = \varphi \circ g$. Then there is a unique morphism $\chi : X \to Z$ with $\chi$ followed by $\iota$ equal to $\varphi$, that is $\iota \circ \chi = \varphi$. Thus the factorisation of $\varphi$ through the closed subscheme $Z$ is asserted on the whole of $X$, not merely on the image of $g$, and it is unique; no flatness, finiteness or separatedness hypotheses occur, and the given factorisation $\psi$ of the restriction enters only through the commutativity hypothesis $h\psi$.
--
--   This is the schematic-image principle in the shape used by its consumers: a morphism from a reduced scheme factors through a closed subscheme as soon as its restriction along a morphism with dense image does so. It is used by [`AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_specMap_subtype_comp_eq`](thm.html#AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_specMap_subtype_comp_eq), where the dense-image morphism comes from a subring inclusion on spectra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_denseRange_of_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_denseRange_of_comp_eq
    {W X Y Z : Scheme.{u}} [IsReduced X] (g : W ⟶ X) (hg : DenseRange g.base)
    (ι : Z ⟶ Y) [IsClosedImmersion ι] (φ : X ⟶ Y)
    (ψ : W ⟶ Z) (hψ : ψ ≫ ι = g ≫ φ) :
    ∃! χ : X ⟶ Z, χ ≫ ι = φ := by sorry
