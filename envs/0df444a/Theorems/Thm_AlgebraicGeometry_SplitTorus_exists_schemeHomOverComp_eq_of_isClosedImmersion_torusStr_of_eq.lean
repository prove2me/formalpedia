-- Prove2me | Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_schemeHomOverComp_eq_of_isClosedImmersion_torusStr_of_eq
-- name    : AlgebraicGeometry.SplitTorus.exists_schemeHomOverComp_eq_of_isClosedImmersion_torusStr_of_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/e73ab2c6-1b62-5aea-846c-e7411c758d88
-- title:
--   Closed immersion of equal-rank split tori lifts κ-points
-- statement:
--   Let $\kappa$ be a field, assumed algebraically closed, and let $t,t'$ be natural numbers with $t'=t$. Write $\mathrm{torusCoord}\,\kappa\,t$ for the group algebra $\kappa[\mathbb Z^t]$, realised as the additive monoid algebra of $\mathrm{Fin}\,t\to\mathbb Z$ over $\kappa$, $\mathrm{torusScheme}\,\kappa\,t$ for its spectrum, and $\mathrm{torusStr}\,\kappa\,t$ for the structure morphism $\mathrm{Spec}$ of the algebra map $\kappa\to\kappa[\mathbb Z^t]$. The datum $F$ is a morphism $F_1\colon \mathrm{torusScheme}\,\kappa\,t'\to\mathrm{torusScheme}\,\kappa\,t$ over $\mathrm{Spec}\,\kappa$, i.e. one satisfying $F_1$ followed by $\mathrm{torusStr}\,\kappa\,t$ equals $\mathrm{torusStr}\,\kappa\,t'$, and $F_1$ is assumed to be a closed immersion. The conclusion is that for every $y$ consisting of a morphism $y_1\colon \mathrm{Spec}\,\kappa\to\mathrm{torusScheme}\,\kappa\,t$ with $y_1$ followed by $\mathrm{torusStr}\,\kappa\,t$ equal to the identity of $\mathrm{Spec}\,\kappa$ — that is, a $\kappa$-point of the rank-$t$ split torus — there is such a $\kappa$-point $z$ of the rank-$t'$ torus, $z_1$ followed by $\mathrm{torusStr}\,\kappa\,t'$ being the identity, with $\mathrm{schemeHomOverComp}\,z\,F=y$, i.e. $z_1$ followed by $F_1$ equals $y_1$. No homomorphism property of $F$ is assumed.
--
--   The statement records, in the $\kappa$-point form its consumers use, that a closed immersion between split tori of equal rank over a field is surjective on sections over the base; the underlying content is that such a closed immersion is in fact an isomorphism. It is used in the construction of the toric lift data for the special fibre of the Néron identity component attached to $J_H$, in [`ModularCurve.JHNeronObjectAtP.exists_baseChange_comp_fst_eq_and_torusFibre_comp_eq_mapDomain_of_iso_of_representsRelSubPic_of_abelianScheme`](thm.html#ModularCurve.JHNeronObjectAtP.exists_baseChange_comp_fst_eq_and_torusFibre_comp_eq_mapDomain_of_iso_of_representsRelSubPic_of_abelianScheme) and [`ModularCurve.JHNeronObjectAtP.exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme`](thm.html#ModularCurve.JHNeronObjectAtP.exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SplitTorus_exists_schemeHomOverComp_eq_of_isClosedImmersion_torusStr_of_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SplitTorus NeronModelInfra

theorem AlgebraicGeometry.SplitTorus.exists_schemeHomOverComp_eq_of_isClosedImmersion_torusStr_of_eq
    (κ : Type) [Field κ] [IsAlgClosed κ] (t t' : ℕ) (ht : t' = t)
    (F : SchemeHomOver (torusStr κ t') (torusStr κ t)) (hF : IsClosedImmersion F.1) :
    ∀ y : SchemeHomOver (𝟙 _) (torusStr κ t),
      ∃ z : SchemeHomOver (𝟙 _) (torusStr κ t'), NeronModelInfra.schemeHomOverComp z F = y := by sorry
