-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_forall_opensInclusion_comp_eq_of_iSup_eq_top_of_disjoint
-- name    : AlgebraicGeometry.Scheme.existsUnique_forall_opensInclusion_comp_eq_of_iSup_eq_top_of_disjoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/9e91b9ac-245e-50c3-a2f7-4a7fabe5910e
-- title:
--   Morphisms glue over a cover by pairwise disjoint opens
-- statement:
--   Let $X$ and $Y$ be schemes, let $\iota$ be an index type, and let $W : \iota \to X.\mathrm{Opens}$ be a family of open subsets of $X$ whose supremum in the lattice of opens is $\top$, i.e. the $W_i$ cover $X$, and which is pairwise disjoint in the sense that $W_i \sqcap W_j = \bot$ whenever $i \neq j$. Suppose given, for each $i$, a morphism of schemes $f_i$ from the open subscheme $W_i$ (with its canonical scheme structure) to $Y$. The conclusion is that there exists a unique morphism of schemes $g : X \to Y$ such that for every $i$ the composite of the open immersion $(W_i).\iota : W_i \to X$ with $g$ equals $f_i$; that is, $g$ restricts to $f_i$ on each $W_i$. Note that the index type $\iota$ lives in an arbitrary universe and no finiteness assumption is imposed; the conclusion is stated as a `∃!`, so both existence of the glued morphism and its uniqueness among morphisms with the stated restrictions are asserted.
--
--   This is the gluing of morphisms of schemes along an open cover, in the special case of a cover by pairwise disjoint opens, where the usual cocycle compatibility on overlaps is automatic. It is used in the construction of a morphism defined piecewise on a clopen decomposition of a base scheme, and is cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_existsUnique_forall_opensInclusion_comp_eq_of_iSup_eq_top_of_disjoint.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.existsUnique_forall_opensInclusion_comp_eq_of_iSup_eq_top_of_disjoint
    {X Y : Scheme.{u}} {ι : Type v} (W : ι → X.Opens) (hW : ⨆ i, W i = ⊤)
    (hdisj : ∀ i j, i ≠ j → W i ⊓ W j = ⊥) (f : ∀ i, (W i : Scheme.{u}) ⟶ Y) :
    ∃! g : X ⟶ Y, ∀ i, (W i).ι ≫ g = f i := by sorry
