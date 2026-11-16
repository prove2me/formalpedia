-- Prove2me | Theorems.Thm_CalibeatBandit_theorem_4_1
-- name    : CalibeatBandit.theorem_4_1
-- status  : Proved
-- author  : @jasonhartline
-- created : 2026-11-15T14:13:49.222681+00:00
-- url     : https://prove2.me/theorems/f740b95c-7ce3-4185-aecc-78a55c4b6616
-- title:
--   Theorem 4.1 — Bandit swap regret lower bound
-- statement:
--   For some absolute constants $c>0$ and $N_0$, for each integer $N\ge N_0$ and each measurable randomized bandit policy on $N$ actions, there is a deterministic oblivious sequence of reward vectors in $[0,1]^N$ for which the expected swap regret at horizon $T=N^4$ is at least $cN^3/(\log N)^6$. The learner’s next action is a measurable function of its private random seed and the rewards it observed on the previous rounds. This lower bound gives the hard instance used by the continuous pricing reduction.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice, STOC 2027 submission 1457, Theorem 4.1 — Bandit swap regret lower bound

import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_swapRegret

open CalibeatBandit MeasureTheory Set

theorem CalibeatBandit.theorem_4_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
        (pick : (t : ℕ) → S → FeedbackHistory t → Fin N),
        (∀ t, Measurable (fun p : S × FeedbackHistory t => pick t p.1 p.2)) →
        ∃ y : ℕ → Fin N → ℝ, (∀ t i, y t i ∈ Icc 0 1) ∧
          c * (N : ℝ) ^ 3 / (Real.log N) ^ 6 ≤
            ∫ s, swapRegret (N ^ 4) y (fun t => pick t s (feedbackHistory (fun i => pick i s) y t)) ∂P := by sorry
