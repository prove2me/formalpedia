-- Prove2me | Theorems.Thm_BanditAlgorithm_exists_policy_tracking_optimal_allocation
-- name    : BanditAlgorithm.exists_policy_tracking_optimal_allocation
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T05:32:10.826075+00:00
-- url     : https://prove2.me/theorems/73f5da7f-5fdd-45e5-a391-8e087bd2b87a
-- title:
--   Existence of a rule tracking an optimal allocation
-- statement:
--   There is a single sampling rule -- one policy, not depending on the environment -- such that for every unit-variance Gaussian bandit with a unique best arm, the empirical allocation $T_i(t)/t$ converges almost surely to **some** optimal allocation of Lattimore--Szepesv\'ari Eq. (33.4).
--
--   This is the constructive half of the D-Tracking guarantee, separated from the allocation theory. It asserts only that the tracked limit is *an* optimal allocation; that it is *the* allocation a given plug-in rule returns is a separate matter, settled by uniqueness of the optimal allocation, and the two are deliberately not bundled here.
--
--   What the construction requires is a policy realising a deterministic function of the observed history, together with the two properties of the greedy tracking rule: that no arm is starved, and that the counts follow the cumulative targets. Concretely one plays, at each round, an arm maximising the shortfall $\sum_{s<t}p_j(s)-T_j(t)$, where $p(s)$ is the plug-in optimal allocation at the current empirical means, mixed with a vanishing fraction of the uniform allocation, $p(s)=(1-k\varepsilon_s)\alpha^*(\hat\mu(s))+\varepsilon_s\mathbf 1$ with $\varepsilon_s=1/(2\sqrt{k^2+s})$.
--
--   The exploration floor is what breaks the circularity between the estimates and the sampling: it forces $T_j(t)\ge\sqrt{k^2+t}-2k+1$ for every arm, deterministically and with no hypothesis on the estimates, which makes the empirical means consistent, which in turn makes the plug-in targets converge. The remaining content is that the greedy rule is realisable as a Markov kernel on histories, so that the trajectory measure is supported on trajectories following it.
-- source:
--   Constructive half of the D-Tracking guarantee of Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Section 2.2 and Proposition 9; line 8 of Algorithm 21 in Lattimore & Szepesvari, Bandit Algorithms (CUP 2020).

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.exists_policy_tracking_optimal_allocation {k : ℕ} [NeZero k] :
    ∃ pol : BanditAlgorithm.BanditPolicy k, ∀ μvec : Fin k → ℝ,
      (∃ istar : Fin k, ∀ j, j ≠ istar → μvec j < μvec istar) →
      ∃ α : Fin k → NNReal,
        BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
            (Set.range (BanditAlgorithm.gaussianBandit (k := k))) α ∧
          ∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
              (BanditAlgorithm.gaussianBandit μvec) pol), ∀ i : Fin k,
            Filter.Tendsto (fun t : ℕ ↦ BanditAlgorithm.trajAllocation i t ω)
              Filter.atTop (nhds ((α i : ℝ))) := by
  sorry
