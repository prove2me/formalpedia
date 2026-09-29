-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper
-- name    : AlgebraicGeometry.Scheme.exists_iso_comp_eq_of_isOpenImmersion_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/13ec2787-4155-5034-9efd-6647b07af0c4
-- title:
--   Open immersion from a smooth proper curve extends to an isomorphism
-- statement:
--   Let $K$ be a field and let $C$ and $C'$ be schemes over $\operatorname{Spec} K$, by means of structure morphisms $c \colon C \to \operatorname{Spec} K$ and $c' \colon C' \to \operatorname{Spec} K$. Assume $C$ is an integral scheme, $c$ is proper and $c$ is smooth of relative dimension $1$; assume $C'$ is an integral scheme, $c'$ is proper and $c'$ is smooth (no dimension being prescribed). Let $U$ be an open subscheme of $C$ whose underlying set is nonempty, let $\iota_U \colon U \to C$ be the inclusion, and let $j \colon U \to C'$ be a morphism that is an open immersion and is a morphism over $K$, i.e. $j$ followed by $c'$ equals $\iota_U$ followed by $c$. Then there is an isomorphism of schemes $e \colon C \xrightarrow{\sim} C'$ which is a morphism over $K$, in the sense that $e$ followed by $c'$ equals $c$, and which extends $j$, in the sense that $\iota_U$ followed by $e$ equals $j$. Uniqueness of $e$ is not asserted.
--
--   This is the statement that a smooth proper curve over a field is determined, together with its identification on any nonempty open piece, by that piece: any open immersion of a nonempty open subscheme of such a curve into a smooth proper integral $K$-scheme is the restriction of an isomorphism. It is used in the comparison of curve models, in the form [`AlgebraicCurve.CurveModel.exists_iso_comp_toBase_eq_placeOfPoint_congr_eq`](thm.html#AlgebraicCurve.CurveModel.exists_iso_comp_toBase_eq_placeOfPoint_congr_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_iso_comp_eq_of_isOpenImmersion_of_isProper
    {K : Type u} [Field K] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (c' : C' ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    [IsIntegral C'] [IsProper c'] [Smooth c']
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (j : (U : Scheme.{u}) ⟶ C') [IsOpenImmersion j] (hj : j ≫ c' = U.ι ≫ c) :
    ∃ e : C ≅ C', e.hom ≫ c' = c ∧ U.ι ≫ e.hom = j := by sorry
