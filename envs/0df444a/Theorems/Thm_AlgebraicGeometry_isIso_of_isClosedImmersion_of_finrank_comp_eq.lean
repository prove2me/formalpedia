-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq
-- name    : AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/831d80a8-ef59-53d8-953b-a3f2e93cd00f
-- title:
--   Equal-rank closed immersion over a base is an isomorphism
-- statement:
--   Let $X$, $Y$ and $S$ be schemes (in a fixed universe), and let $i : X \to Y$, $g : Y \to S$ and $f : X \to S$ be morphisms with $i$ followed by $g$ equal to $f$. Assume $i$ is a closed immersion, that $g$ is finite, flat and locally of finite presentation, and that $f$ is flat and locally of finite presentation. Assume further that the two rank functions on the base agree: for every point $s$ of $S$, the rank $f.\mathrm{finrank}\ s$ of $f$ at $s$ equals the rank $g.\mathrm{finrank}\ s$ of $g$ at $s$. The conclusion is that $i$ is an isomorphism of schemes. Finiteness of $f$ is not assumed; it follows from the hypotheses on $i$ and $g$, and is recovered inside the proof when needed.
--
--   This is the scheme-theoretic statement that a closed subscheme of a finite flat (finitely presented) $S$-scheme which is itself flat and finitely presented over $S$ of the same rank at every point of $S$ must be the whole scheme. It is the engine behind [`AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_eq`](thm.html#AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_eq) and the comparison of ideal sheaf data [`AlgebraicGeometry.Scheme.IdealSheafData.eq_of_le_of_forall_finrank_subschemeIota_comp_eq`](thm.html#AlgebraicGeometry.Scheme.IdealSheafData.eq_of_le_of_forall_finrank_subschemeIota_comp_eq), and is used further downstream in the analysis of isogenies of fake elliptic curves with extra level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq.lean

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq
    {X Y S : Scheme.{u}} (i : X ⟶ Y) (g : Y ⟶ S) (f : X ⟶ S) (w : i ≫ g = f)
    [IsClosedImmersion i] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : ↥S, f.finrank s = g.finrank s) :
    IsIso i := by sorry
