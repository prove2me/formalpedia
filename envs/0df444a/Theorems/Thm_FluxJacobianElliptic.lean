-- Prove2me | Theorems.Thm_FluxJacobianElliptic
-- name    : FluxJacobianElliptic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:15:33.354629+00:00
-- url     : https://prove2.me/theorems/0dda0b18-cae1-49ff-9ba8-1bbc68e2a303
-- title:
--   Flux Jacobian Elliptic: Flux Jacobian Elliptic
-- statement:
--   Everything the paper asserts about the flux Jacobian on an annulus away from the origin
--   (paper lines 170-174: "On the annulus `delta/2 ≤ |xi| ≤ C₀`, the map `A` is smooth with
--   bounded derivatives, and the matrix `D_xi A(xi)` ... is uniformly elliptic, with ellipticity
--   bounds depending only on `p, delta`").  Five clauses, for `1 < p < 2` and `0 < a ≤ b`:
--
--   1. `FluxJacobian p ξ` really is the Frechet derivative of `PFlux p` at every `ξ ≠ 0`;
--   2. `FluxJacobian p` is `C^∞` on the open set `{ζ | ζ ≠ 0}`;
--   3. the ellipticity constants `lam = (p-1) * b^(p-2)` and `Lam = a^(p-2)` satisfy
--      `0 < lam ≤ Lam` — they depend only on `p, a, b`, hence (when applied with `a = delta/2`
--      and `b = C₀`) only on `p` and `delta`, as the paper claims;
--   4. UNIFORM ELLIPTICITY on the annulus `a ≤ ‖ξ‖ ≤ b`, in exactly the shape
--      `DivFormSchauderInput` consumes: `lam * ‖w‖^2 ≤ ⟪D_ξ A(ξ) w, w⟫` and
--      `‖D_ξ A(ξ) w‖ ≤ Lam * ‖w‖`;
--   5. BOUNDED DERIVATIVES of every order on the annulus;
--   6. the flux `PFlux p` itself is `C^∞` on `{ζ | ζ ≠ 0}` — the first half of the paper's sentence,
--      "the map `A` is smooth with bounded derivatives", and what makes the composition
--      `x ↦ A_p(Dv x)` smooth wherever `Dv` is smooth and nonvanishing.
--
--   The two constants are the ones pm-0010 fixes, and the direction matters: for `p < 2` the
--   exponent `p - 2` is negative, so `t ↦ t^(p-2)` is DECREASING, the scalar factor `‖ξ‖^(p-2)`
--   is smallest at `‖ξ‖ = b` and largest at `‖ξ‖ = a`.  The algebraic core of clause 4 is
--   `(p-1)‖w‖^2 ≤ ‖w‖^2 + (p-2) ⟪ξ,w⟫^2/‖ξ‖^2`, from Cauchy-Schwarz and `p - 2 < 0`; the upper
--   bound is sharp and comes from the orthogonal splitting of `w` along and across `ξ`, on which
--   `I + (p-2) ξ⊗ξ/‖ξ‖^2` acts by `p - 1` and by `1` respectively.
--
--   In clause 5 the ambient `iteratedFDeriv` is the genuine iterated derivative at points of the
--   annulus, because `{ζ | ζ ≠ 0}` is open and iterated derivatives are local.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/FluxJacobianElliptic.lean#L33-L119
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/FluxJacobianElliptic.lean#L33-L119

import Definitions.Def_PHigherOrder_FluxJacobian
import Definitions.Def_PHigherOrder_FluxJacobianIsDeriv
import Definitions.Def_PHigherOrder_FluxJacobianAnnulusEllipticity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Definitions.Def_PHigherOrder_FluxJacobianElliptic
import Theorems.Thm_FluxJacobianAnnulusEllipticity
import Theorems.Thm_FluxJacobianIsDeriv

set_option autoImplicit false

theorem FluxJacobianElliptic (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) :
    (∀ ξ : Plane, ξ ≠ 0 → HasFDerivAt (PFlux p) (FluxJacobian p ξ) ξ)
      ∧ ContDiffOn ℝ (⊤ : ℕ∞) (FluxJacobian p) {ζ : Plane | ζ ≠ 0}
      ∧ 0 < (p - 1) * b ^ (p - 2) ∧ (p - 1) * b ^ (p - 2) ≤ a ^ (p - 2)
      ∧ (∀ ξ : Plane, a ≤ ‖ξ‖ → ‖ξ‖ ≤ b → ∀ w : Plane,
          (p - 1) * b ^ (p - 2) * ‖w‖ ^ 2 ≤ inner ℝ (FluxJacobian p ξ w) w
            ∧ ‖FluxJacobian p ξ w‖ ≤ a ^ (p - 2) * ‖w‖)
      ∧ (∀ j : ℕ, ∃ M : ℝ, 0 < M ∧ ∀ ξ : Plane, a ≤ ‖ξ‖ → ‖ξ‖ ≤ b →
          ‖iteratedFDeriv ℝ j (FluxJacobian p) ξ‖ ≤ M)
      ∧ ContDiffOn ℝ (⊤ : ℕ∞) (PFlux p) {ζ : Plane | ζ ≠ 0} := by sorry
