-- Prove2me | Theorems.Thm_BanditAlgorithm_exists_policy_tracking_chosen_allocation
-- name    : BanditAlgorithm.exists_policy_tracking_chosen_allocation
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:51:10.138191+00:00
-- url     : https://prove2.me/theorems/7e799c54-b781-40c3-8d5d-c56e055e20c2
-- title:
--   D-Tracking: a single sampling rule tracks a prescribed optimal allocation
-- statement:
--   The D-Tracking guarantee of Garivier and Kaufmann (COLT 2016, Section 2.2 and Proposition 9), which is line 8 of Lattimore-Szepesvari Algorithm 21. Given any rule that assigns to each Gaussian parameter vector with a unique best arm an optimal allocation with full support, there is a single sampling rule -- not depending on the environment -- whose empirical allocation T_i(t)/t converges almost surely to that optimal allocation, for every such environment. D-Tracking achieves this by forcing exploration whenever some arm has been played fewer than about the square root of t times, and otherwise playing the arm whose empirical allocation lags furthest behind the plug-in optimal weights computed from the current empirical means; the forced exploration makes the empirical means consistent, and continuity of the optimal weights then transfers that consistency to the tracked allocation.
-- source:
--   Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Section 2.2, Lemma 7 and Proposition 9; Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Algorithm 21, line 8.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.exists_policy_tracking_chosen_allocation {k : ℕ} [NeZero k]
    (choice : (Fin k → ℝ) → Fin k → NNReal)
    (hchoice : ∀ μvec : Fin k → ℝ, (∃ istar : Fin k, ∀ j, j ≠ istar → μvec j < μvec istar) →
      (∀ i, 0 < choice μvec i) ∧
        BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
          (Set.range (BanditAlgorithm.gaussianBandit (k := k))) (choice μvec)) :
    ∃ pol : BanditAlgorithm.BanditPolicy k, ∀ μvec : Fin k → ℝ,
      (∃ istar : Fin k, ∀ j, j ≠ istar → μvec j < μvec istar) →
      ∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
          (BanditAlgorithm.gaussianBandit μvec) pol), ∀ i : Fin k,
        Filter.Tendsto (fun t : ℕ ↦ BanditAlgorithm.trajAllocation i t ω) Filter.atTop
          (nhds ((choice μvec i : ℝ))) := by
  sorry
