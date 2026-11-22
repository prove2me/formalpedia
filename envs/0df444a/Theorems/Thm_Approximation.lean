-- Prove2me | Theorems.Thm_Approximation
-- name    : Approximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:30.205197+00:00
-- url     : https://prove2.me/theorems/2f848aba-8d23-465c-9b64-004d458a3491
-- title:
--   Approximation: Approximation
-- statement:
--   Paper eq:approximation (paper line 227), the estimate the main theorem's final assembly
--   rests on: for every `p`-harmonic `v` on `B_1` with `v(0) = 0` and `‖v‖_{L^∞(B_1)} ≤ 1`, the
--   degree-`k` Taylor polynomial of `v` at the origin has bounded coefficients and approximates `v`
--   to order `sigma = k + beta`, with a constant depending only on `p, k, beta`.
--
--   This is the node that BUILDS THE CHAIN OF RADII, once, before the case split: it takes `delta`
--   and `theta` from `IterationStep` — both produced before `v`, which is what keeps the final
--   constant uniform — instantiates `IterationSequence` with
--
--     `Good R = (0 < R ∧ R ≤ 1 ∧ ∀ y, ‖y‖ < R → |v y| ≤ R ^ sigma)`,
--     `Cont R = (R ^ (1 - sigma) * ‖gradient v 0‖ ≤ delta)`,
--
--   runs `IterationDichotomy` on the resulting chain, and then cases on whether `Dv(0)` vanishes.
--   Both branch nodes take the chain as hypotheses precisely so that this happens here and once:
--   `IterationDichotomy`'s first conclusion is an equivalence about one SPECIFIC chain, so the
--   dichotomy and the two branches must all speak about the same `R`.
--
--   The two clauses are diagonal, as everything carrying higher-order derivatives in this
--   development is, and the error clause is pointwise in `‖y‖`.  The proof is short because the
--   mathematics lives in the two branches; per the note on cases in the substantiveness rubric that
--   is the proper shape for an aggregator over two meaningfully different branches.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/Approximation.lean#L28-L123
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/Approximation.lean#L28-L123

import Definitions.Def_PHigherOrder_ApproxFiniteCase
import Definitions.Def_PHigherOrder_ApproxInfiniteCase
import Definitions.Def_PHigherOrder_IterationDichotomy
import Definitions.Def_PHigherOrder_IterationSequence
import Definitions.Def_PHigherOrder_IterationStep
import Definitions.Def_PHigherOrder_Approximation
import Theorems.Thm_ApproxFiniteCase
import Theorems.Thm_ApproxInfiniteCase
import Theorems.Thm_IterationDichotomy
import Theorems.Thm_IterationSequence
import Theorems.Thm_IterationStep

set_option autoImplicit false

theorem Approximation (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hLR : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (hsm : SmoothAwayFromCriticalInput p) (hS : DivFormSchauderInput)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g →
        (∀ y ∈ Metric.ball (0 : Plane) 1, |v y| ≤ 1) → v 0 = 0 →
        (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ w : Plane,
            |iteratedFDeriv ℝ j v 0 (fun _ => w)| ≤ C * ‖w‖ ^ j)
          ∧ (∀ y : Plane, ‖y‖ < 1 →
              |v y - TaylorPoly k v 0 y| ≤ C * ‖y‖ ^ ((k : ℝ) + β)) := by sorry
