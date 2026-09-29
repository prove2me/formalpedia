-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_eq_top_and_nonempty_module_iso_and_nonempty_invModule_iso_of_disjoint_range_support
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.comap_eq_top_and_nonempty_module_iso_and_nonempty_invModule_iso_of_disjoint_range_support
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/65766b63-d832-5e91-97fa-110be9882b2f
-- title:
--   Ideal sheaf pulled back off its support becomes the unit ideal
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe), let $I$ be an ideal sheaf datum on $Y$ (a compatible family of ideals of the rings of sections over the affine opens of $Y$), and let $f \colon X \to Y$ be a morphism of schemes. Assume that the range of the underlying continuous map `f.base` is disjoint, as a subset of the topological space of $Y$, from the support of $I$. The conclusion is threefold: first, the pulled-back ideal sheaf datum $I.\mathrm{comap}\, f$ on $X$ is the top element, i.e. the unit ideal; second, the sheaf of $\mathcal{O}_X$-modules attached to $I.\mathrm{comap}\, f$ — namely the kernel of the canonical map from the unit sheaf of modules on $X$ to the pushforward, along the closed immersion of the subscheme cut out by that ideal, of the unit sheaf of modules there — is isomorphic to the unit object $\mathbb{1}$ of the monoidal category $X.\mathrm{Modules}$; and third, its dual, the internal hom from that module into the unit, is likewise isomorphic to the unit. The two isomorphism assertions are stated as nonemptiness of the respective types of isomorphisms, so no canonical choice is made.
--
--   In classical language: if the image of $f$ misses the support of $\mathcal{O}_Y/\mathcal{I}$, then the inverse-image ideal $f^{*}\mathcal{I}\cdot\mathcal{O}_X$ is all of $\mathcal{O}_X$ and both $\mathcal{O}_X(-f^{-1}Z)$ and $\mathcal{O}_X(f^{-1}Z)$ are trivial, $Z$ being the closed subscheme defined by $\mathcal{I}$. It is used to show that the pullback of either of these two sheaves along such a morphism is the unit sheaf, as needed when a line bundle on a model over a discrete valuation ring is twisted by a divisor supported in the closed fibre and then restricted away from that divisor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_eq_top_and_nonempty_module_iso_and_nonempty_invModule_iso_of_disjoint_range_support.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_eq_top_and_nonempty_module_iso_and_nonempty_invModule_iso_of_disjoint_range_support
    {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    (h : Disjoint (Set.range f.base) (I.support : Set Y)) :
    I.comap f = ⊤ ∧ Nonempty ((I.comap f).module ≅ 𝟙_ X.Modules) ∧ Nonempty ((I.comap f).invModule ≅ 𝟙_ X.Modules) := by sorry
