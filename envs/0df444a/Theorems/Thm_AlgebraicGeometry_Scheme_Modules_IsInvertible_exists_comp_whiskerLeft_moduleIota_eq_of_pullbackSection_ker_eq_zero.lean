-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_comp_whiskerLeft_moduleIota_eq_of_pullbackSection_ker_eq_zero
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_comp_whiskerLeft_moduleIota_eq_of_pullbackSection_ker_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/ab1ac5a6-5025-5df7-8d11-4d3cca20ab21
-- title:
--   Sections vanishing on a closed subscheme lift to L(-Z)
-- statement:
--   Let $X$ and $Z$ be schemes and let $f : Z \to X$ be a closed immersion. Let $L$ be an $\mathcal{O}_X$-module (an object of `X.Modules`) that is invertible in the sense of `Scheme.Modules.IsInvertible`: every point of $X$ has an open neighbourhood $U$ such that the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module of the structure sheaf of $U$. Let $s : \mathbf{1}_{X.\mathrm{Modules}} \to L$ be a global section, i.e. a morphism from the unit module, and suppose that its pullback to $Z$ vanishes, where the pullback is formed as the inverse of the canonical isomorphism identifying the pullback of the unit with the unit of $Z$, followed by the image of $s$ under the pullback functor along $f$. Write $f.\mathrm{ker}$ for the ideal sheaf data of the closed immersion $f$, and let $f.\mathrm{ker}.\mathrm{module}$ be the associated $\mathcal{O}_X$-module, namely the kernel of the map from the unit module of $X$ to the pushforward along the inclusion of the associated closed subscheme of that subscheme's unit module, with $f.\mathrm{ker}.\mathrm{module}\iota$ its inclusion into the unit. The conclusion is that $s$ factors through this ideal: there exists $s' : \mathbf{1}_{X.\mathrm{Modules}} \to L \otimes f.\mathrm{ker}.\mathrm{module}$ such that $s'$, followed by $L \lhd f.\mathrm{ker}.\mathrm{module}\iota$, followed by the right unitor $\rho_L$, equals $s$.
--
--   This is the standard statement that a global section of an invertible module whose restriction to a closed subscheme $Z$ vanishes is a section of $L(-Z) = L \otimes \mathcal{I}_Z$. It is used in the analysis of two glued curves, in [`AlgebraicGeometry.TwoGluedCurves.subsingleton_H1_and_support_zeroSchemeIdeal_subset_of_restrict`](thm.html#AlgebraicGeometry.TwoGluedCurves.subsingleton_H1_and_support_zeroSchemeIdeal_subset_of_restrict).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_comp_whiskerLeft_moduleIota_eq_of_pullbackSection_ker_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_comp_whiskerLeft_moduleIota_eq_of_pullbackSection_ker_eq_zero
    {X Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ X.Modules ⟶ L)
    (hs : Scheme.Modules.pullbackSection f s = 0) :
    ∃ s' : 𝟙_ X.Modules ⟶ L ⊗ f.ker.module, s' ≫ (L ◁ f.ker.moduleι) ≫ (ρ_ L).hom = s := by sorry
