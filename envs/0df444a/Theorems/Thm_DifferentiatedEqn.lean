-- Prove2me | Theorems.Thm_DifferentiatedEqn
-- name    : DifferentiatedEqn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:18:00.177498+00:00
-- url     : https://prove2.me/theorems/16276275-f6bd-45c3-a273-603dfecf8504
-- title:
--   Differentiated Eqn: Differentiated Eqn
-- statement:
--   The differentiated equation (paper line 177): "Differentiating the equation gives
--   `div (D_xi A(Dv) D(v_{x_i})) = 0` in `B_{2 tau}`".
--
--   Formalized WITHOUT any pointwise divergence operator, which Mathlib does not have: the
--   conclusion is that the directional derivative `d_e v x = ⟪Dv x, e⟫` is a weak solution of the
--   linear divergence-form equation with coefficient field `A x = D_xi A_p(Dv x)`, in the sense of
--   `IsLinearDivSol`, with its own classical gradient as weak gradient.  Taking `e` to be the two
--   standard basis vectors recovers the paper's two equations for `v_{x_1}` and `v_{x_2}`.
--
--   The route stays inside the WEAK equation: substitute the test function `d_e ψ` into
--   `IsPHarm.eqn` — a directional derivative of a test function is again a test function —
--   integrate by parts once in the direction `e` to move `d_e` from the test function onto the
--   flux, and apply the chain rule `d_e (A_p(Dv)) = D_xi A_p(Dv)[d_e(Dv)]`.  The only derivative
--   symmetry used is `d_e (Dv) = D (d_e v)`, i.e. symmetry of the SECOND derivative of `v`.
--
--   Hypotheses.  `v` is `p`-harmonic on the open set `U` with its own CLASSICAL gradient as weak
--   gradient, which `PHarmWeakGradClassical` supplies from any weak gradient once `v` is `C^1`
--   (so `IsPHarm.openOmega` also makes a separate `IsOpen U` hypothesis redundant); `v` is `C^∞`
--   on `U`, which `SmoothAwayFromCriticalInput` supplies given the gradient annulus; and `Dv` does
--   not vanish on `U`, from `GradientAnnulus`, which is what makes `A_p` differentiable along `Dv`
--   with `D_xi A_p(Dv)` as its derivative there.  The range `1 < p < 2` is the paper's standing
--   assumption (paper line 102) and is what lets `FluxJacobianElliptic` be invoked for the
--   differentiability and smoothness of the flux away from the origin.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/DifferentiatedEqn.lean#L30-L173
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/DifferentiatedEqn.lean#L30-L173

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_FluxJacobianElliptic
import Definitions.Def_PHigherOrder_IsLinearDivSol
import Definitions.Def_PHigherOrder_ClassicalGradIsWeakGrad
import Definitions.Def_PHigherOrder_DirectionalIntegrationByParts
import Definitions.Def_PHigherOrder_DifferentiatedEqn
import Theorems.Thm_ClassicalGradIsWeakGrad
import Theorems.Thm_DirectionalIntegrationByParts
import Theorems.Thm_FluxJacobianElliptic

set_option autoImplicit false

theorem DifferentiatedEqn (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (U : Set Plane)
    (v : Plane → ℝ)
    (hv : IsPHarm p U v (gradient v)) (hsm : ContDiffOn ℝ (⊤ : ℕ∞) v U)
    (hne : ∀ x ∈ U, gradient v x ≠ 0) (e : Plane) :
    IsLinearDivSol U (fun x => FluxJacobian p (gradient v x))
      (fun x => inner ℝ (gradient v x) e)
      (fun x => gradient (fun y => inner ℝ (gradient v y) e) x) := by sorry
