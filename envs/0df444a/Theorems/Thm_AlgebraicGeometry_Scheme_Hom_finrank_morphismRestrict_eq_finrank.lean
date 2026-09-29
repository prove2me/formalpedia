-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_morphismRestrict_eq_finrank
-- name    : AlgebraicGeometry.Scheme.Hom.finrank_morphismRestrict_eq_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/d03d0690-a695-5a50-9668-038504a8c9e7
-- title:
--   Rank of a finite morphism is unchanged by restriction to an open
-- statement:
--   Let $X$ and $S$ be schemes (in a fixed universe), and let $f \colon X \to S$ be a morphism which is finite. Let $W$ be an open subscheme of $S$, and assume that the restricted morphism $f \mid_W \colon f^{-1}(W) \to W$, obtained by base change along the open immersion $W \hookrightarrow S$, is flat; note that flatness is assumed only for this restriction, not for $f$ itself. Let $s$ be a point of $S$ lying in $W$, so that it determines a point $\langle s, hs\rangle$ of the scheme $W$. The assertion is that Mathlib's rank invariant `Scheme.Hom.finrank` takes the same value on these two data: the rank of the restriction $f \mid_W$ at the point of $W$ corresponding to $s$ equals the rank of $f$ at $s$ as a point of $S$.
--
--   This records that the rank of a finite morphism at a point is local on the base, in the form needed to compare the rank of $f$ with that of its restriction over an open where flatness is available; Mathlib's comparison lemmas for ranks instead assume flatness over the whole base. It is used in the project when a finite morphism of curves or of relative Picard data is flat only over an open locus, for instance in [`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_functionField_of_flat_morphismRestrict`](thm.html#AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_functionField_of_flat_morphismRestrict) and in the rank computations for Igusa-type models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_finrank_morphismRestrict_eq_finrank.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.finrank_morphismRestrict_eq_finrank
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] (W : S.Opens) [Flat (f ∣_ W)] (s : S) (hs : s ∈ W) :
    (f ∣_ W).finrank ⟨s, hs⟩ = f.finrank s := by sorry
