-- Prove2me | Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field
-- name    : AlgebraicGeometry.isReduced_of_smooth_over_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/97eb85f5-9ed9-57ba-98c5-308b219b0408
-- title:
--   Schemes smooth over a field are reduced
-- statement:
--   Let $k$ be a field, let $Z$ be a scheme, and let $g \colon Z \to \operatorname{Spec} k$ be a morphism of schemes, where $\operatorname{Spec} k$ is the spectrum of $k$ regarded as a commutative ring (all objects in a single universe $u$). Assume that $g$ satisfies Mathlib's morphism property `Smooth`, i.e. $g$ is a smooth morphism of schemes. The conclusion is `IsReduced Z`: the scheme $Z$ is reduced, meaning that the ring of sections over every open subset of $Z$ has no nonzero nilpotents. Note that no finiteness, separatedness or quasi-compactness hypothesis is imposed on $Z$, and no hypothesis on $k$ beyond being a field; in particular $k$ is not assumed perfect or algebraically closed, and the conclusion is reducedness of $Z$ itself rather than the stronger geometric regularity of $Z$ over $k$.
--
--   This is the standard fact that smoothness over a field forces reducedness (a weak form of the statement that a scheme smooth over a field is geometrically regular); the hypothesis that the base is a field is essential, since the identity of the spectrum of the dual numbers is smooth. Within the project it is used to recognise reducedness of smooth schemes in the arguments on relative effective Cartier divisors and relative Picard groups of curves, for instance in [`AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper) and [`AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_polarisedChartModule_fibre_of_support_subset_of_twoGluedSmoothCurveDegenerations_of_not_smooth`](thm.html#AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_polarisedChartModule_fibre_of_support_subset_of_twoGluedSmoothCurveDegenerations_of_not_smooth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isReduced_of_smooth_over_field.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry

theorem AlgebraicGeometry.isReduced_of_smooth_over_field {k : Type u} [Field k]
    {Z : Scheme.{u}} {g : Z ⟶ Spec (.of k)} (hg : Smooth g) : IsReduced Z := by sorry
