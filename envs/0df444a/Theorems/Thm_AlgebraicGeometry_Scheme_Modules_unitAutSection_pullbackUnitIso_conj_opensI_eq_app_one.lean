-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one
-- name    : AlgebraicGeometry.Scheme.Modules.unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/b0e5c1c4-b955-5eed-8555-296b1ba64c7c
-- title:
--   Restricting an automorphism of mathcal O_Y to an open
-- statement:
--   Let $Y$ be a scheme, let $W$ be an open subset of $Y$, and let $\psi$ be an isomorphism of the unit sheaf of modules $\mathcal O_Y$ over the sheaf of rings `Y.ringCatSheaf` with itself. Pull $\psi$ back along the inclusion $\iota_W \colon W \hookrightarrow Y$ of the open subscheme and conjugate by the canonical trivialisation `Scheme.Modules.pullbackUnitIso W.ι`, the isomorphism $\iota_W^{*}\mathcal O_Y \cong \mathcal O_W$ obtained from the canonical map `SheafOfModules.pullbackObjUnitToUnit`, which is invertible; the result is an automorphism of the unit sheaf on the scheme $W$, namely the composite of the inverse trivialisation, the pullback of $\psi$, and the trivialisation. The assertion is that the element of $\Gamma(Y, W)$ attached to this automorphism by `Scheme.Modules.unitAutSection W` — by definition its value on the section $1 \in \Gamma(W, \top)$, taken over the top open of $W$ and transported to $\Gamma(Y, W)$ along `Scheme.Opens.topIso` — coincides with the value $(\psi_W)(1)$ of the component of $\psi$ over $W$ on the unit section $1 \in \Gamma(Y, W)$.
--
--   This identifies the section attached to an automorphism of the structure sheaf, read on the open subscheme $W$, with the naive value $\psi_W(1) \in \Gamma(Y,W)$; so the global-to-chart comparison of two trivialisations of a line bundle is simply restriction of sections. It is used in [`AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_appTop_eq_unitAutSection`](thm.html#AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_appTop_eq_unitAutSection), in the Čech-theoretic treatment of deformations of line bundles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one.lean

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

theorem AlgebraicGeometry.Scheme.Modules.unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one
    {Y : Scheme.{u}} (W : Y.Opens)
    (ψ : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf) :
    Scheme.Modules.unitAutSection W
        ((Scheme.Modules.pullbackUnitIso W.ι).symm ≪≫ (Scheme.Modules.pullback W.ι).mapIso ψ ≪≫
          Scheme.Modules.pullbackUnitIso W.ι) =
      (ψ.hom.val.app (op W)).hom (1 : Y.presheaf.obj (op W)) := by sorry
