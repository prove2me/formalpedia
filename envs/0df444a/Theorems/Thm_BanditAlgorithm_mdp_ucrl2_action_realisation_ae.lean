-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_ucrl2_action_realisation_ae
-- name    : BanditAlgorithm.mdp_ucrl2_action_realisation_ae
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T23:14:23.872448+00:00
-- url     : https://prove2.me/theorems/65321448-a8e3-4c50-8b6f-8f1aabc8e9f8
-- title:
--   UCRL2 almost surely plays the action its policy prescribes
-- statement:
--   Fix $S$ states, $A\ge1$ actions, a horizon $n$, a confidence level $\delta$, a known reward function $r$, a finite MDP $M$ and an initial state distribution. Under the law of the trajectory produced by interconnecting $M$ with the UCRL2 policy, almost every trajectory $h$ satisfies, at every round $t<n$,
--   $$A_t=f_{\tau(t)}(S_t),$$
--   where $f_{\tau(t)}$ is the greedy action map of the optimistic plan for the confidence balls formed from the transitions observed strictly before the start $\tau(t)$ of the phase current at time $t$, those balls being read off the *whole* trajectory $h$.
--
--   The statement is what makes the deterministic regret analysis applicable to the realised trajectory. Its two ingredients are that the selection kernels of the policy are Dirac kernels at that action map, so the action of a round is determined by the history, and that the counts the policy computes from the prefix of $t$ rounds together with the currently observed state agree with the counts computed from the full trajectory, which is the bookkeeping identity that the transition out of round $i$ is visible exactly when round $i+1$ is recorded.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Sections 38.1 and 38.5 (the interconnection of a policy with an MDP, and UCRL2), printed pp. 516-526 / PDF pp. 525-535.

import Definitions.Def_UCRL2Algorithm

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_ucrl2_action_realisation_ae
    (S A n : ℕ) [NeZero A] (δ : ℝ) (r : Fin S → Fin A → ℝ)
    (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) :
    mdpMeasure M μ0 (ucrl2Policy n δ r) n
        {h : MDPTrajectory S A n | ∀ t : Fin n,
          (h t).2 = mdpOptimisticActionMap r
            (fun x a ↦ mdpConfidenceSet h (mdpPhaseStart h t.val + 1) n δ x a)
            (h t).1}ᶜ
      = 0 := by
  sorry
