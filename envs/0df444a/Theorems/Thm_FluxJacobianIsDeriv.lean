-- Prove2me | Theorems.Thm_FluxJacobianIsDeriv
-- name    : FluxJacobianIsDeriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:12:55.264937+00:00
-- url     : https://prove2.me/theorems/cea57402-bfa2-4bf4-9f48-d99b485ff761
-- title:
--   Flux Jacobian Is Deriv: Flux Jacobian Is Deriv
-- statement:
--   THE FLUX JACOBIAN REALLY IS THE DERIVATIVE OF THE FLUX, away from the origin: for every
--   `p : ℝ` and every `ξ ≠ 0`, the `p`-flux `A_p` is Frechet differentiable at `ξ` with
--
--   `D A_p(ξ) = FluxJacobian p ξ`.
--
--   This is the definitional link between the two definition nodes `PFlux` and `FluxJacobian`.  They
--   are declared independently -- the second is a formula for a continuous linear map, not derived
--   from the first -- so the statement that one is the derivative of the other is a theorem and
--   everything downstream rests on it: the coefficient field of the differentiated equation IS
--   `D_ξ A_p` composed with the gradient, and that reading is only legitimate once this is proved.
--
--   No restriction on `p` is needed, and none is taken.  The lemma holds for every real `p`; the
--   hypothesis `1 < p < 2` that the rest of the development carries is about ellipticity constants
--   and plays no part here, which is why this clause is the one that mentions neither radius of an
--   annulus.
--
--   The route is through the SQUARED norm rather than the norm.  `ζ ↦ ‖ζ‖` is not differentiable at
--   the origin and its derivative elsewhere is awkward, whereas `ζ ↦ ‖ζ‖^2` is smooth everywhere
--   with derivative `2 innerSL ℝ ζ` given explicitly by the library.  Writing the flux as
--   `A_p(ζ) = (‖ζ‖^2)^((p-2)/2) ζ` -- an identity valid at EVERY `ζ`, the origin included -- turns
--   the computation into the real power rule composed with that derivative, times the identity, and
--   the product rule then assembles exactly the two summands of `FluxJacobian`.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/FluxJacobianIsDeriv.lean#L26-L79
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/FluxJacobianIsDeriv.lean#L26-L79

import Definitions.Def_PHigherOrder_FluxJacobian
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Definitions.Def_PHigherOrder_FluxJacobianIsDeriv
set_option autoImplicit false

theorem FluxJacobianIsDeriv (p : ℝ) :
    ∀ ξ : Plane, ξ ≠ 0 → HasFDerivAt (PFlux p) (FluxJacobian p ξ) ξ := by sorry
