-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop
-- name    : AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_conj_app_top_one_eq_appTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/d7cfd05c-633a-5a8d-a403-190cd97d89b4
-- title:
--   Conjugated pullback automorphism of the unit sheaf on global sections
-- statement:
--   Let $S,S'$ be schemes (in a fixed universe) and let $p \colon S' \to S$ be a morphism of schemes. Let $e$ be a self-isomorphism of the unit module `SheafOfModules.unit S.ringCatSheaf`, i.e. of $\mathcal O_S$ regarded as a sheaf of modules over the sheaf of rings of $S$. Write $\mathrm{pullbackUnitIso}\,p$ for the canonical isomorphism $p^{*}\mathcal O_S \cong \mathcal O_{S'}$, obtained by inverting the canonical morphism from the pullback of the unit to the unit associated with the ring-sheaf morphism underlying $p$. Conjugating the pullback $p^{*}e$ by this isomorphism, that is forming $(\mathrm{pullbackUnitIso}\,p)^{-1}$ followed by $(\mathrm{pullback}\,p).\mathrm{mapIso}\,e$ followed by $\mathrm{pullbackUnitIso}\,p$, yields a self-isomorphism of `SheafOfModules.unit S'.ringCatSheaf`. The assertion is that the component of its forward direction at the opposite of the top open of $S'$, applied to the unit section $1 \in \Gamma(S', \mathcal O_{S'})$, equals the image under $p^{\sharp} =$ `p.appTop` of the element $(e.\mathrm{hom}.\mathrm{val}.\mathrm{app}\,(\mathrm{op}\,\top))(1) \in \Gamma(S, \mathcal O_S)$.
--
--   An automorphism of the unit module on a scheme is multiplication by a unit global section, and this lemma records that passing to the pullback along $p$ and trivialising $p^{*}\mathcal O_S$ replaces that section by its image under $p^{\sharp}$ on global sections. It is the basic compatibility used when comparing transition sections and their discrepancies across different opens or different schemes in the Čech description of line bundles, and is cited by the results on Čech trivialisations and their transition functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_conj_app_top_one_eq_appTop
    {S S' : Scheme.{u}} (p : S' ⟶ S)
    (e : SheafOfModules.unit S.ringCatSheaf ≅ SheafOfModules.unit S.ringCatSheaf) :
    ((((Scheme.Modules.pullbackUnitIso p).symm ≪≫ (Scheme.Modules.pullback p).mapIso e ≪≫
          Scheme.Modules.pullbackUnitIso p :
            SheafOfModules.unit S'.ringCatSheaf ≅ SheafOfModules.unit S'.ringCatSheaf)).hom.val.app (op ⊤)).hom
        (1 : S'.presheaf.obj (op ⊤)) =
      p.appTop.hom ((e.hom.val.app (op ⊤)).hom (1 : S.presheaf.obj (op ⊤))) := by sorry
