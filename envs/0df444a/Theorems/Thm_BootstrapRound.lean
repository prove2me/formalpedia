-- Prove2me | Theorems.Thm_BootstrapRound
-- name    : BootstrapRound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:11:39.967312+00:00
-- url     : https://prove2.me/theorems/39fd73ff-d4e7-47cf-93e1-893d2569bb55
-- title:
--   Bootstrap Round: Bootstrap Round
-- statement:
--   One round of the paper's Schauder bootstrap, in the form the induction of lem:noncritical
--   consumes it.
--
--   The round takes `C^{j,kappa}` bounds on a coefficient field `A` on a ball `B_r`, together with
--   the differentiated equations -- each directional derivative `d_e v` is a weak solution of
--   `div (A D(d_e v)) = 0` on `B_r`, in the sense of `IsLinearDivSol` -- and returns
--   `C^{j+2,kappa}` bounds on the scalar function `v` itself on the smaller ball `B_{r'}`.
--
--   Three things happen, none of them supplied by `DivFormSchauderInput` on its own.  First the
--   directional derivatives are NORMALIZED: the Schauder input needs a solution bounded by `1`, and
--   `d_e v` is only bounded by `b`, so it is divided by `c = b + 1`; this needs
--   `IsLinearDivSol` to be stable under a positive scalar multiple, which is five conditions each
--   holding by homogeneity.  Second the input is applied, in both coordinate directions, and the
--   scaling undone.  Third the bounds on the two directional derivatives are REASSEMBLED into bounds
--   on `v` one order higher, which costs a factor `2` -- the number of basis directions of the plane
--   -- and is where the round's gain of one order becomes a gain on `v`.
--
--   The conclusion starts at order `1`: the round produces orders `1` through `j+2`, and a bound at
--   order `0` is a bound on `v` itself, which no Schauder estimate is needed for.  As in the Schauder
--   input, `N` is quantified before `v` and `A`.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/BootstrapRound.lean#L25-L250
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/BootstrapRound.lean#L25-L250

import Definitions.Def_PHigherOrder_DivFormSchauderInput
import Definitions.Def_PHigherOrder_GradientFieldOrderShift
import Definitions.Def_PHigherOrder_IsLinearDivSol
import Definitions.Def_PHigherOrder_BootstrapRound
import Theorems.Thm_GradientFieldOrderShift

set_option autoImplicit false

theorem BootstrapRound (hS : DivFormSchauderInput)
    (j : ℕ) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLL : lam ≤ Lam)
    (M b : ℝ) (hM : 0 < M) (hb : 0 < b)
    (r r' : ℝ) (hr' : 0 < r') (hrr : r' < r) :
    ∃ N : ℝ, 0 < N ∧
      ∀ (v : Plane → ℝ) (A : Plane → (Plane →L[ℝ] Plane)),
        ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) →
        (∀ x ∈ Metric.ball (0 : Plane) r, ‖gradient v x‖ ≤ b) →
        (∀ x ∈ Metric.ball (0 : Plane) r, ∀ ξ : Plane,
            lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ ∧ ‖A x ξ‖ ≤ Lam * ‖ξ‖) →
        ContDiffOn ℝ (j : ℕ∞) A (Metric.ball 0 r) →
        (∀ i ≤ j, ∀ x ∈ Metric.ball (0 : Plane) r, ‖iteratedFDeriv ℝ i A x‖ ≤ M) →
        (∀ x ∈ Metric.ball (0 : Plane) r, ∀ y ∈ Metric.ball (0 : Plane) r,
            ‖iteratedFDeriv ℝ j A x - iteratedFDeriv ℝ j A y‖ ≤ M * ‖x - y‖ ^ κ) →
        (∀ e : Plane, IsLinearDivSol (Metric.ball 0 r) A
            (fun x => inner ℝ (gradient v x) e)
            (fun x => gradient (fun y => inner ℝ (gradient v y) e) x)) →
        (∀ m, 1 ≤ m → m ≤ j + 2 → ∀ x ∈ Metric.ball (0 : Plane) r',
            ‖iteratedFDeriv ℝ m v x‖ ≤ N)
          ∧ (∀ x ∈ Metric.ball (0 : Plane) r', ∀ y ∈ Metric.ball (0 : Plane) r',
              ‖iteratedFDeriv ℝ (j + 2) v x - iteratedFDeriv ℝ (j + 2) v y‖
                ≤ N * ‖x - y‖ ^ κ) := by sorry
