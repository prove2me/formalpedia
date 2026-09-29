-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le
-- name    : AlgebraicGeometry.IsClosedImmersion.exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/e8584b83-1d20-5aef-b8bc-4016827eadc5
-- title:
--   Factoring Spec(mathcal O_{A,y}/J) through a closed immersion
-- statement:
--   Let $A$ and $K$ be schemes (in the bottom universe), let $\kappa : K \to A$ be a morphism which is a closed immersion, let $y'$ be a point of $K$, write $y = \kappa(y')$ for its image, and let $J$ be an ideal of the stalk $\mathcal O_{A,y} =$ `A.presheaf.stalk (κ.base y')`. The assertion is an equivalence. On one side: there exists a morphism of schemes $t : \operatorname{Spec}(\mathcal O_{A,y}/J) \to K$ such that $t$ followed by $\kappa$ equals the morphism $\operatorname{Spec}$ of the quotient map $\mathcal O_{A,y} \to \mathcal O_{A,y}/J$ followed by the canonical morphism $\operatorname{Spec}\mathcal O_{A,y} \to A$ attached to the point $y$ (`A.fromSpecStalk`); in other words, the canonical morphism $\operatorname{Spec}(\mathcal O_{A,y}/J) \to A$ factors through $\kappa$. On the other side: the kernel of the induced map on stalks $\kappa^{\sharp}_{y'} : \mathcal O_{A,y} \to \mathcal O_{K,y'}$ is contained in $J$. Note that the factorisation asserted is through the given point $y'$ of $K$, not merely through some point of $K$ above $y$.
--
--   This is the standard infinitesimal-lifting criterion for a closed subscheme: the ideal sheaf of $\kappa$, localised at $y$, is the kernel of the map on stalks, and a thickening $\operatorname{Spec}(\mathcal O_{A,y}/J)$ of $y$ lands in $K$ exactly when $J$ contains that kernel. It is used in the `Polarisation` development, where slices of a scheme at a stalk are compared with closed subschemes (in `exists_free_complex_cech_sliceAt_stalk_and_seesaw`, `finrank_H0_baseChange_residue_sliceAt_stalk_eq_one` and `forall_exists_pullbackSection_eq_iff_exists_comp_eq_of_mem_range`).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le
    {A K : Scheme.{0}} (κ : K ⟶ A) [IsClosedImmersion κ] (y' : K)
    (J : Ideal (A.presheaf.stalk (κ.base y'))) :
    (∃ t : Spec (CommRingCat.of ((A.presheaf.stalk (κ.base y')) ⧸ J)) ⟶ K,
        t ≫ κ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ A.fromSpecStalk (κ.base y')) ↔
      RingHom.ker (κ.stalkMap y').hom ≤ J := by sorry
