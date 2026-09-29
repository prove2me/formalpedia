-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_units_forall_app_eq_smul_of_iso_unit
-- name    : AlgebraicGeometry.Scheme.Modules.exists_units_forall_app_eq_smul_of_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/2c9b1111-4cc0-5c07-beae-02f5cedfcb8e
-- title:
--   Automorphisms of the unit module are multiplication by global units
-- statement:
--   Let $X$ be a scheme (in a fixed universe) and let $\gamma$ be an isomorphism, in the category `X.Modules` of sheaves of modules over the sheaf of rings `X.ringCatSheaf` of $X$, from the unit module `SheafOfModules.unit X.ringCatSheaf` (that is, $\mathcal{O}_X$ viewed as a module over itself) to itself. The assertion is that there exists a unit $u$ of the ring $\Gamma(X, \top)$ of global sections of $\mathcal{O}_X$ such that for every open subset $U$ of $X$ and every section $s \in \Gamma(\mathcal{O}_X, U)$ of the unit module over $U$, the value at $U$ of the forward component $\gamma.\mathrm{hom}$ of the isomorphism, applied to $s$, equals the restriction of $u$ along the inclusion $U \le \top$ (that is, the image of $u$ under `X.presheaf.map` applied to the opposite of `homOfLE le_top`) acting on $s$ by scalar multiplication. Thus every automorphism of $\mathcal{O}_X$ as an $\mathcal{O}_X$-module is multiplication by a globally defined invertible function; only the forward direction of $\gamma$ occurs in the conclusion, the inverse serving to make $u$ invertible.
--
--   This is the standard identification of the automorphism group of the structure sheaf as a module over itself with the units of the ring of global functions, the base case of the description of isomorphisms between invertible modules. It is used in the construction of the relative Picard functor through rigidified line bundles, where it supplies the uniqueness of an isomorphism between two trivialisations of an invertible module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_units_forall_app_eq_smul_of_iso_unit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_units_forall_app_eq_smul_of_iso_unit
    {X : Scheme.{u}} (γ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ (U : X.Opens) (s : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
      Scheme.Modules.Hom.app γ.hom U s = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (u : Γ(X, ⊤)) • s := by sorry
