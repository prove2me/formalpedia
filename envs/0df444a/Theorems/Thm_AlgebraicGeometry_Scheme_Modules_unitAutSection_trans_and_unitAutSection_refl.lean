-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_trans_and_unitAutSection_refl
-- name    : AlgebraicGeometry.Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/87b09db6-1fa3-518a-abbe-b42eaba6ad7d
-- title:
--   Multiplicativity of the section attached to an automorphism of the unit module
-- statement:
--   Let $Y$ be a scheme and let $W$ be an open subset of $Y$, regarded also as an open subscheme. For an isomorphism $e$ of the unit sheaf of modules `SheafOfModules.unit` over the sheaf of rings $\mathcal{O}_W$ of that open subscheme with itself, the section $\sigma(e) =$ `Scheme.Modules.unitAutSection W e` $\in \Gamma(Y, W)$ is by definition obtained by evaluating the component of $e.\mathrm{hom}$ at the top open $\top$ of $W$ on the unit element $1 \in \Gamma(W, \top)$ and transporting the result along the canonical isomorphism `W.topIso` between $\Gamma(W, \top)$ and $\Gamma(Y, W)$. The theorem asserts the conjunction of two facts: first, for all such isomorphisms $e$ and $e'$ one has $\sigma(e \mathbin{\text{≪≫}} e') = \sigma(e)\,\sigma(e')$, where $e \mathbin{\text{≪≫}} e'$ is the composite isomorphism ($e$ followed by $e'$), the product being taken in the ring $\Gamma(Y, W)$; second, $\sigma(\mathrm{id}) = 1$ for the identity isomorphism. Thus $\sigma$ is a monoid homomorphism from the automorphisms of the unit module, composed in diagrammatic order, to the multiplicative monoid of $\Gamma(Y, W)$.
--
--   This records the standard identification of automorphisms of the trivial line bundle on an open set with units of its ring of sections, in the multiplicative form needed to compare trivialisations. It is used in the Čech description of invertible modules and of the Picard obstruction, where `unitAutSection` is applied to composites of chart isomorphisms and the resulting transition sections must be multiplied and inverted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_trans_and_unitAutSection_refl.lean

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

theorem AlgebraicGeometry.Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl
    {Y : Scheme.{u}} (W : Y.Opens) :
    (∀ e e' : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf,
        Scheme.Modules.unitAutSection W (e ≪≫ e') =
          Scheme.Modules.unitAutSection W e * Scheme.Modules.unitAutSection W e') ∧
      Scheme.Modules.unitAutSection W (Iso.refl _) = 1 := by sorry
