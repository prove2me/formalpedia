-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackPushforwardAdjunction_unit_app_eq_of_comp_eq
-- name    : AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction_unit_app_eq_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/bf905b84-a6f6-5c8b-a0a5-c701d362ba23
-- title:
--   Transitivity of the pullback–pushforward adjunction unit
-- statement:
--   Let $Z$, $Z'$, $X$ be schemes (in a fixed universe), let $t \colon Z \to Z'$, $\iota' \colon Z' \to X$ and $\iota \colon Z \to X$ be morphisms of schemes with $t$ followed by $\iota'$ equal to $\iota$, and let $N$ be a sheaf of $\mathcal{O}_X$-modules, i.e. an object of `X.Modules`. Then the component at $N$ of the unit of the adjunction $\iota^{*} \dashv \iota_{*}$, namely $\eta^{\iota}_{N} \colon N \to \iota_{*}\iota^{*}N$, is equal to the composite of the following six morphisms: the unit $\eta^{\iota'}_{N} \colon N \to \iota'_{*}\iota'^{*}N$; the image under $\iota'_{*}$ of the unit $\eta^{t}_{\iota'^{*}N} \colon \iota'^{*}N \to t_{*}t^{*}\iota'^{*}N$; the component at $t^{*}\iota'^{*}N$ of the comparison isomorphism `pushforwardComp t ι'`, from $\iota'_{*}t_{*}$ to the pushforward along the composite; the image under the pushforward along the composite of the component at $N$ of the comparison isomorphism `pullbackComp t ι'`, from $t^{*}\iota'^{*}N$ to the pullback of $N$ along the composite; the image under the same pushforward of the component at $N$ of the transport `pullbackCongr h` of pullback functors along the equality $h$; and finally the component at $\iota^{*}N$ of the transport `pushforwardCongr h` of pushforward functors along $h$.
--
--   This is the usual transitivity (cocycle) compatibility of the adjunctions $f^{*} \dashv f_{*}$ for sheaves of modules under composition of morphisms of schemes, expressed on units rather than on the functors themselves. It is used in the comparison of pullbacks of invertible modules along adic thickenings, where the units of the successive restrictions have to be matched with the unit of the total restriction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullbackPushforwardAdjunction_unit_app_eq_of_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction_unit_app_eq_of_comp_eq
    {Z Z' X : Scheme.{u}} (t : Z ⟶ Z') (ι' : Z' ⟶ X) (ι : Z ⟶ X) (h : t ≫ ι' = ι) (N : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app N =
      (Scheme.Modules.pullbackPushforwardAdjunction ι').unit.app N
        ≫ (Scheme.Modules.pushforward ι').map
            ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app ((Scheme.Modules.pullback ι').obj N))
        ≫ (Scheme.Modules.pushforwardComp t ι').hom.app
            ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback ι').obj N))
        ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackComp t ι').hom.app N)
        ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackCongr h).hom.app N)
        ≫ (Scheme.Modules.pushforwardCongr h).hom.app ((Scheme.Modules.pullback ι).obj N) := by sorry
