-- Prove2me | Theorems.Thm_ApproxFiniteCase
-- name    : ApproxFiniteCase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:37:16.082978+00:00
-- url     : https://prove2.me/theorems/580bd889-b73b-4124-9046-a7572d58fa40
-- title:
--   Approx Finite Case: Approx Finite Case
-- statement:
--   The FINITE branch of eq:approximation (paper lines 260-281): the iteration stops at a first
--   index `L`, so `Dv_L(0)` exceeds `delta`, `Noncritical` applies to the rescaled solution `v_L`,
--   and transporting its conclusions back through the dilation gives eq:coefficients and eq:small
--   for `v` itself.
--
--   As in `ApproxInfiniteCase` the chain of radii is a HYPOTHESIS written out in full, so that
--   `Approximation` can build it once and hand the same chain to both branches.  Here the two-sided
--   bound `hsand` is GUARDED BY `l < L`, not unconditional: `IterationDichotomy`'s second conclusion
--   needs the continuation condition at every index, which is exactly what fails at `L`, so in this
--   branch only the indices below `L` carry it.
--
--   `theta <= 1` is carried explicitly.  It is free from `IterationStep`, whose `theta` is below
--   `1/4`, and it is needed: without an upper bound on `theta` the comparison of consecutive
--   constructed scales in the far regime gives no bound at all.
--
--   The error clause is POINTWISE in `‖y‖`, for the reason recorded in `ApproxInfiniteCase`.  Its
--   proof splits at `‖y‖ = tau * R L` with `tau` from `Noncritical`: below, eq:small via
--   `TaylorRemainder` on `v_L` transported by `TaylorPolyRescale`; above, the paper's
--   `max{r, R_L}^sigma` comparison, which pointwise in `‖y‖` collapses to two inequalities needing
--   only `tau * R L <= ‖y‖`, `0 < tau < 1` and `j <= sigma`.  Note `‖y‖ > 0` is load-bearing there,
--   and it is available because `‖y‖ >= tau * R L > 0`; the case `y = 0` is handled separately.
--
--   `C` is produced BEFORE `v`, from `p, k, beta, delta, theta` alone, which is what makes the
--   constant of `Approximation` uniform.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/ApproxFiniteCase.lean#L33-L311
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/ApproxFiniteCase.lean#L33-L311

import Definitions.Def_PHigherOrder_IMRegularityInput
import Definitions.Def_PHigherOrder_Noncritical
import Definitions.Def_PHigherOrder_PHarmNormalize
import Definitions.Def_PHigherOrder_TaylorPolyDeriv
import Definitions.Def_PHigherOrder_TaylorPolyFarBound
import Definitions.Def_PHigherOrder_TaylorPolyRescale
import Definitions.Def_PHigherOrder_TaylorRemainder
import Definitions.Def_PHigherOrder_ApproxFiniteCase
import Theorems.Thm_Noncritical
import Theorems.Thm_PHarmNormalize
import Theorems.Thm_TaylorPolyDeriv
import Theorems.Thm_TaylorPolyFarBound
import Theorems.Thm_TaylorPolyRescale
import Theorems.Thm_TaylorRemainder

set_option autoImplicit false

theorem ApproxFiniteCase (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (F : FirstOrderEstimateInput p) (hsm : SmoothAwayFromCriticalInput p)
    (hS : DivFormSchauderInput) (hIM : IMRegularityInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p)
    (δ : ℝ) (hδ : 0 < δ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g → v 0 = 0 →
        ∀ (R : ℕ → ℝ) (L : ℕ), R 0 = 1 → (∀ l : ℕ, 0 < R l) → (∀ l : ℕ, R l ≤ 1) →
          (∀ (l : ℕ) (y : Plane), ‖y‖ < R l → |v y| ≤ R l ^ ((k : ℝ) + β)) →
          (∀ l < L, θ * R l ≤ R (l + 1) ∧ R (l + 1) ≤ R l / 4) →
          δ < R L ^ (1 - ((k : ℝ) + β)) * ‖gradient v 0‖ →
          (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ w : Plane,
              |iteratedFDeriv ℝ j v 0 (fun _ => w)| ≤ C * ‖w‖ ^ j)
            ∧ (∀ y : Plane, ‖y‖ < 1 →
                |v y - TaylorPoly k v 0 y| ≤ C * ‖y‖ ^ ((k : ℝ) + β)) := by sorry
