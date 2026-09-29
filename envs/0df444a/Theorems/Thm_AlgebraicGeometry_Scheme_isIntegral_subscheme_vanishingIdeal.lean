-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal
-- name    : AlgebraicGeometry.Scheme.isIntegral_subscheme_vanishingIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/66bd160f-a09e-531b-a8aa-79707f6f957b
-- title:
--   Reduced induced subscheme on an irreducible closed set is integral
-- statement:
--   Let $V$ be a scheme and let $Z$ be a closed subset of the underlying topological space of $V$ (an element of the lattice `Closeds` of closed sets), and assume that $Z$, viewed as a subset of $V$, is irreducible, i.e. nonempty and not the union of two closed subsets each properly contained in it. Consider the ideal sheaf datum `Scheme.IdealSheafData.vanishingIdeal Z` attached to $Z$, whose component on an affine open $U \subseteq V$ is the vanishing ideal of the subset $Z \cap U$ of $\operatorname{Spec} \Gamma(V, U)$, and let `(Scheme.IdealSheafData.vanishingIdeal Z).subscheme` be the closed subscheme of $V$ that this datum cuts out, that is, the reduced induced structure on $Z$. The assertion is that this scheme is integral in Mathlib's sense, `IsIntegral`.
--
--   This is the standard fact that the reduced induced closed subscheme structure on an irreducible closed subset of a scheme is integral. It serves as the entry point for dévissage arguments that filter a module or coherent sheaf along integral closed subschemes, and is used in the construction of dévissage steps for $\mathcal{O}$-module presheaves and in the extraction of integral closed subschemes supported on irreducible components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.lean

import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.isIntegral_subscheme_vanishingIdeal {V : Scheme.{u}} (Z : Closeds V) (hZ : IsIrreducible (Z : Set V)) : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by sorry
