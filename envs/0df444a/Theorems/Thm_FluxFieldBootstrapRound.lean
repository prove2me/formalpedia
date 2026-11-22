-- Prove2me | Theorems.Thm_FluxFieldBootstrapRound
-- name    : FluxFieldBootstrapRound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:27:07.508844+00:00
-- url     : https://prove2.me/theorems/a49a763f-6c04-4abb-9d79-285ccd6253a6
-- title:
--   Flux Field Bootstrap Round: Flux Field Bootstrap Round
-- statement:
--   ONE SCHAUDER BOOTSTRAP ROUND FOR THE `p`-HARMONIC EQUATION, on a pair of nested balls.
--
--   Given the paper's first-order input `F`, the divergence-form Schauder input `hS`, an order `i`, an
--   annulus `0 < a ≤ b`, radii `0 < r' < r` and a constant `D > 0`, there is `D' ≥ 1` -- produced
--   BEFORE the solution -- such that any `v` carrying the structural package on `ball 0 r` at order
--   `i+1` with constant `D` carries the order-`(i+2)` sup and Holder bounds on the smaller
--   `ball 0 r'` with constant `D'`.  One order is gained per round; that is the mechanism of the
--   paper's lem:noncritical.
--
--   This is the COMPOSITE of two existing nodes with the ellipticity and annulus conversion in
--   between, and neither of them states it.  `CoeffFieldFromScalarBounds` turns `C^{i+1,kappa}`
--   bounds on the SCALAR `v` into `C^{i,kappa}` bounds on the coefficient field
--   `A x = D_xi A_p(Dv x)`; `BootstrapRound` takes a coefficient field AS GIVEN and returns the next
--   scalar order.  The present node PRODUCES that field from `v` -- composing the flux Jacobian with
--   the gradient, reading its ellipticity constants off `FluxJacobianElliptic` on the annulus, and
--   bounding its derivatives there -- and only then runs the round.  So its hypotheses are about `v`
--   alone, which is the form a bootstrap induction can actually carry.
--
--   Everything the round needs beyond `v` is built here rather than passed in: the ellipticity
--   constants `lam`, `Lam`, the uniform bound `CPhi` on the flux Jacobian's derivatives up to order
--   `i+1` on the annulus, and the diameter bound `d := 2 * r` for `ball 0 r`.  In particular the node
--   is stated on ONE PAIR of radii, with no radius sequence and no cutoff index: a caller running an
--   induction supplies its own consecutive radii.  The Holder exponent is `F.kappa`, carried as `κ`
--   with `hκdef` so a caller that has already named it can pass its own.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/FluxFieldBootstrapRound.lean#L30-L163
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/FluxFieldBootstrapRound.lean#L30-L163

import Definitions.Def_PHigherOrder_BootstrapRound
import Definitions.Def_PHigherOrder_CoeffFieldFromScalarBounds
import Definitions.Def_PHigherOrder_FluxJacobianElliptic
import Definitions.Def_PHigherOrder_GradientAnnulus
import Definitions.Def_PHigherOrder_FluxFieldBootstrapRound
import Theorems.Thm_BootstrapRound
import Theorems.Thm_CoeffFieldFromScalarBounds
import Theorems.Thm_FluxJacobianElliptic
import Theorems.Thm_GradientAnnulus

set_option autoImplicit false

theorem FluxFieldBootstrapRound (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (F : FirstOrderEstimateInput p) (hS : DivFormSchauderInput)
    (κ : ℝ) (hκdef : κ = F.kappa) (i : ℕ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (r r' : ℝ) (hr' : 0 < r') (hrr : r' < r) (D : ℝ) (hD : 0 < D) :
    ∃ D' : ℝ, 0 < D' ∧ 1 ≤ D' ∧
      ∀ (v : Plane → ℝ) (V : Set Plane),
      IsOpen V → Convex ℝ V → (∀ ζ ∈ V, a ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ b) →
      (∀ x ∈ Metric.ball (0 : Plane) r, gradient v x ∈ V) →
      ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) →
      (∀ x ∈ Metric.ball (0 : Plane) r, |v x| ≤ 1) →
      (∀ x ∈ Metric.ball (0 : Plane) r, ‖gradient v x‖ ≤ F.C₀) →
      (∀ m ≤ i + 1, ∀ x ∈ Metric.ball (0 : Plane) r,
          ‖iteratedFDeriv ℝ m v x‖ ≤ D) →
      (∀ x ∈ Metric.ball (0 : Plane) r, ∀ y ∈ Metric.ball (0 : Plane) r,
          ‖iteratedFDeriv ℝ (i + 1) v x - iteratedFDeriv ℝ (i + 1) v y‖
            ≤ D * ‖x - y‖ ^ κ) →
      (∀ e : Plane, IsLinearDivSol (Metric.ball 0 r)
          (fun x => FluxJacobian p (gradient v x))
          (fun x => inner ℝ (gradient v x) e)
          (fun x => gradient (fun y => inner ℝ (gradient v y) e) x)) →
      (∀ m ≤ i + 2, ∀ x ∈ Metric.ball (0 : Plane) r',
          ‖iteratedFDeriv ℝ m v x‖ ≤ D')
        ∧ (∀ x ∈ Metric.ball (0 : Plane) r',
            ∀ y ∈ Metric.ball (0 : Plane) r',
            ‖iteratedFDeriv ℝ (i + 2) v x - iteratedFDeriv ℝ (i + 2) v y‖
              ≤ D' * ‖x - y‖ ^ κ) := by sorry
