-- Prove2me | Theorems.Thm_FluxJacobianAnnulusEllipticity
-- name    : FluxJacobianAnnulusEllipticity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:02.374944+00:00
-- url     : https://prove2.me/theorems/8761c6a7-44a9-4586-b794-300e34f87228
-- title:
--   Flux Jacobian Annulus Ellipticity: Flux Jacobian Annulus Ellipticity
-- statement:
--   UNIFORM ELLIPTICITY OF THE p-FLUX JACOBIAN ON AN ANNULUS, in exactly the shape the
--   divergence-form Schauder layer consumes.  For `1 < p < 2`, `0 < a <= b`, every `ξ` with
--   `a <= ‖ξ‖ <= b` and every `w`,
--
--   `(p-1) b^(p-2) ‖w‖^2 <= ⟪D_ξ A_p(ξ) w, w⟫`  and  `‖D_ξ A_p(ξ) w‖ <= a^(p-2) ‖w‖`.
--
--   The two constants depend only on `p, a, b` -- never on `ξ` -- which is the uniformity the
--   bootstrap needs, and the DIRECTION of the dependence is the content: for `p < 2` the exponent
--   `p - 2` is NEGATIVE, so `t ↦ t^(p-2)` is decreasing and the scalar factor `‖ξ‖^(p-2)` is
--   smallest at the outer radius `b` and largest at the inner radius `a`.  Hence the lower constant
--   carries `b` and the upper one carries `a`, and not the other way round.
--
--   The algebraic core of the lower bound is `(p-1)‖w‖^2 <= ‖w‖^2 + (p-2) ⟪ξ,w⟫^2/‖ξ‖^2`, which
--   follows from Cauchy-Schwarz together with `p - 2 < 0`.  The upper bound is sharp: it comes from
--   the orthogonal splitting of `w` along and across `ξ`, on which `I + (p-2) ξ⊗ξ/‖ξ‖^2` acts by
--   `p - 1` and by `1` respectively, so its operator norm is `max{p-1, 1} = 1` for `p < 2`.
--
--   This is the clause the paper's lem:noncritical destructures and feeds to the Schauder input, so
--   it is a named fact of the development rather than a step of a longer argument.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/FluxJacobianAnnulusEllipticity.lean#L22-L96
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/FluxJacobianAnnulusEllipticity.lean#L22-L96

import Definitions.Def_PHigherOrder_FluxJacobian
import Definitions.Def_PHigherOrder_FluxJacobianAnnulusEllipticity
set_option autoImplicit false

theorem FluxJacobianAnnulusEllipticity (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    ∀ ξ : Plane, a ≤ ‖ξ‖ → ‖ξ‖ ≤ b → ∀ w : Plane,
    (p - 1) * b ^ (p - 2) * ‖w‖ ^ 2 ≤ inner ℝ (FluxJacobian p ξ w) w
      ∧ ‖FluxJacobian p ξ w‖ ≤ a ^ (p - 2) * ‖w‖ := by sorry
