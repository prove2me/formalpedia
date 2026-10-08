-- Prove2me | Theorems.Thm_ForwardRM_Cutoffs_DPi_increasing_in_time
-- name    : ForwardRM.Cutoffs.DPi_increasing_in_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:59:39.855186+00:00
-- url     : https://prove2.me/theorems/da7d7c54-fe57-49cc-8ac0-6b860c1250ab
-- title:
--   Lemma 4 — under decreasing demand and time-decreasing future cutoffs, DΠ^k_{t+1}(y¹) ≥ DΠ^k_t(y¹)
-- statement:
--   Suppose demand $N_t$ is weakly decreasing in the usual stochastic order. Let $t\ge 1$ with $t+1\le T-1$, let $k\ge 1$, and suppose the future cutoffs are decreasing in time: $x^j_s\ge x^j_{s+1}$ for all $s\in\{t+1,\dots,T-1\}$ and $j\in\{1,\dots,k\}$. Then for every $y^1\in[\underline v,\bar v]$
--
--   $$
--   D\Pi^k_{t+1}(y^1)\ge D\Pi^k_t(y^1).
--   $$
--
--   The incentive to sell today rather than tomorrow grows over time, because fewer entrants arrive later and the future cutoffs fall. This is the comparison that drives the induction in the proof of Theorem 2.
--
--   **Formalization Note** $D\Pi^k_{t+1}$ involves period $t+2$, hence $t+2\le T$. The cutoffs $x^j_s$ are the model's cutoffs (deterministic by Theorem 1).
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 17, Lemma 4 (proof in Appendix A.2, pp. 34–36)

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction
import Definitions.Def_ForwardRM_Cutoffs_Cutoff

namespace ForwardRM.Cutoffs

/-- Lemma 4 (Board–Skrzypacz, p. 17): if `N_t` is weakly decreasing in the usual stochastic order
and the future cutoffs are decreasing in time, `x^j_s ≥ x^j_{s+1}` for `s ∈ {t+1, …, T−1}` and
`j ≤ k`, then `DΠ^k_{t+1}(y¹) ≥ DΠ^k_t(y¹)` for every `y¹ ∈ [v̲, v̄]`
(here `t + 1 ≤ T − 1`, so that `DΠ^k_{t+1}` is defined). -/
theorem DPi_increasing_in_time (M : Model) (hD : M.DecreasingDemand) (t k : ℕ) (ht : 1 ≤ t)
    (htT : t + 2 ≤ M.T) (hk : 1 ≤ k)
    (hfut : ∀ s j, t + 1 ≤ s → s + 1 ≤ M.T → 1 ≤ j → j ≤ k → M.cutoff (s + 1) j ≤ M.cutoff s j) :
    ∀ y1 ∈ Set.Icc M.vlo M.vhi, M.DPi t k y1 ≤ M.DPi (t + 1) k y1 := by sorry

end ForwardRM.Cutoffs
