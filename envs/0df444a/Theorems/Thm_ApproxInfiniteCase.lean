-- Prove2me | Theorems.Thm_ApproxInfiniteCase
-- name    : ApproxInfiniteCase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:32:41.853911+00:00
-- url     : https://prove2.me/theorems/a1b8e7ce-dae8-49cc-a1c3-9309844543f1
-- title:
--   Approx Infinite Case: Approx Infinite Case
-- statement:
--   The INFINITE branch of eq:approximation (paper lines 252-258): the iteration never stops,
--   which happens exactly when `Dv(0) = 0`, and then the degree-`k` Taylor polynomial of `v` at the
--   origin vanishes identically while `v` itself decays at the rate `sigma = k + beta`.
--
--   The chain of radii is a HYPOTHESIS, written out in full, not a construction: `Approximation`
--   builds it once and passes it to both branches, because `IterationDichotomy`'s first conclusion
--   is an equivalence about one SPECIFIC chain and a branch node that rebuilt its own could not be
--   lined up with it.  Correspondingly this node imports neither iteration node.
--
--   The decay clause is POINTWISE in `‖y‖`, not indexed by a radius: `‖y‖ < 1` is the paper's
--   `0 < r ≤ 1` read as a supremum over the open ball, and the pointwise form implies the paper's
--   display at once by `‖y‖ ≤ r`, whereas the radius-indexed form needs a limit `r ↓ ‖y‖` to get
--   back here.  The consumers need the pointwise form.
--
--   `hleft` is UNCONDITIONAL here: in this branch the continuation condition holds at every index,
--   so the combining node has already discharged the guard that `IterationSequence` attaches to it.
--   Note that no upper bound on `theta` is needed, and none is assumed: the decay constant is
--   `theta ^ (-sigma)` whatever `theta > 0` is.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/ApproxInfiniteCase.lean#L25-L110
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/ApproxInfiniteCase.lean#L25-L110

import Definitions.Def_PHigherOrder_IMRegularityInput
import Definitions.Def_PHigherOrder_PHarmRestrict
import Definitions.Def_PHigherOrder_PHarmWeakGradClassical
import Definitions.Def_PHigherOrder_Rigidity
import Definitions.Def_PHigherOrder_TaylorPoly
import Definitions.Def_PHigherOrder_ApproxInfiniteCase
import Theorems.Thm_PHarmRestrict
import Theorems.Thm_PHarmWeakGradClassical
import Theorems.Thm_Rigidity

set_option autoImplicit false

theorem ApproxInfiniteCase (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hLR : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p)
    (θ : ℝ) (hθ0 : 0 < θ)
    (v : Plane → ℝ) (g : Plane → Plane) (hph : IsPHarm p (Metric.ball 0 1) v g)
    (hv0 : v 0 = 0) (hcrit : gradient v 0 = 0)
    (R : ℕ → ℝ) (hR0 : R 0 = 1) (hRpos : ∀ l : ℕ, 0 < R l)
    (hGood : ∀ (l : ℕ) (y : Plane), ‖y‖ < R l → |v y| ≤ R l ^ ((k : ℝ) + β))
    (hleft : ∀ l : ℕ, θ * R l ≤ R (l + 1))
    (hlim : Filter.Tendsto R Filter.atTop (nhds 0)) :
    (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ w : Plane, iteratedFDeriv ℝ j v 0 (fun _ => w) = 0)
      ∧ TaylorPoly k v 0 = 0
      ∧ ∀ y : Plane, ‖y‖ < 1 → |v y| ≤ θ ^ (-((k : ℝ) + β)) * ‖y‖ ^ ((k : ℝ) + β) := by sorry
