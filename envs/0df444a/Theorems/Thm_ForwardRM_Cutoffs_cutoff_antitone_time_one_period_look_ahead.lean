-- Prove2me | Theorems.Thm_ForwardRM_Cutoffs_cutoff_antitone_time_one_period_look_ahead
-- name    : ForwardRM.Cutoffs.cutoff_antitone_time_one_period_look_ahead
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:59:45.305982+00:00
-- url     : https://prove2.me/theorems/18a2631b-035f-4c38-b6cb-56672a8d18a2
-- title:
--   Theorem 2 — under weakly decreasing demand the cutoffs x^k_t fall over time and are the unique roots of DΠ^k_t
-- statement:
--   Suppose the number of entrants $N_t$ is weakly decreasing in the usual stochastic order: $N_{t+1}\le_{st}N_t$ for all $t\in\{1,\dots,T-1\}$. Then for every number of units $k\ge 1$:
--
--   1. the optimal cutoffs are decreasing in $t$: $x^k_{t+1}\le x^k_t$ for $1\le t\le T-1$;
--   2. allocations satisfy the one-period-look-ahead property and are uniquely characterized by
--
--   $$
--   D\Pi^k_t(x^k_t)=0 ,
--   $$
--
--   that is, for $1\le t\le T-1$ the seller is indifferent between selling to the cutoff type today and waiting one period and allocating that unit tomorrow, and $x^k_t$ is the only $y\in[\underline v,\bar v]$ with $D\Pi^k_t(y)=0$.
--
--   Under decreasing demand the optimal dynamic mechanism is therefore described by local, one-period indifference conditions, which become differential equations in the continuous-time limit of §5.
--
--   **Formalization Note** $D\Pi^k_t$ compares period $t$ with period $t+1$ and is only defined for $t\le T-1$. The cutoffs $x^k_t$ are those of the model, characterized by Theorem 1.
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 17, Theorem 2 (one-period-look-ahead property defined on p. 17; proof p. 18)

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction
import Definitions.Def_ForwardRM_Cutoffs_Cutoff

namespace ForwardRM.Cutoffs

/-- Theorem 2 (Board–Skrzypacz, p. 17): if `N_t` is weakly decreasing in the usual stochastic
order, then for every `k ≥ 1` the optimal cutoffs `x^k_t` are decreasing in `t`, and in every period
`t ≤ T − 1` the seller is indifferent between selling to the cutoff type today and waiting one
period and selling that unit tomorrow (`DΠ^k_t(x^k_t) = 0`, the one-period-look-ahead property),
`x^k_t` being the unique root of `DΠ^k_t` in `[v̲, v̄]`. -/
theorem cutoff_antitone_time_one_period_look_ahead (M : Model) (hD : M.DecreasingDemand)
    (k : ℕ) (hk : 1 ≤ k) :
    (∀ t, 1 ≤ t → t + 1 ≤ M.T → M.cutoff (t + 1) k ≤ M.cutoff t k) ∧
    (∀ t, 1 ≤ t → t + 1 ≤ M.T →
      M.DPi t k (M.cutoff t k) = 0 ∧
      ∀ y ∈ Set.Icc M.vlo M.vhi, M.DPi t k y = 0 → y = M.cutoff t k) := by sorry

end ForwardRM.Cutoffs
