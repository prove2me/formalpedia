-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_ucrl2_bias_martingale_deviation
-- name    : BanditAlgorithm.mdp_ucrl2_bias_martingale_deviation
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T23:14:39.266775+00:00
-- url     : https://prove2.me/theorems/25b2e4c5-2ecd-4046-8026-b8bc707c5dc6
-- title:
--   Martingale deviation of the UCRL2 bias term
-- statement:
--   Fix $S\ge2$ states, $A\ge1$ actions, a horizon $n\ge1$, a confidence level $\delta\in(0,1)$, a known reward function $r$ with values in $[0,1]$, a finite MDP $M$ with reward function $r$ and diameter $D(M)\ge1$, and an initial state distribution. There is an event $E$ of probability at least $1-\delta/2$ under the law of the trajectory produced by UCRL2 such that on $E$, and on the confidence good event, the sum of the increments of the bias martingale is at most $D(M)\sqrt{2n\log(2/\delta)}$:
--   $$\sum_{t<n-1}\Big(\sum_{s'}P_{A_t}(S_t,s')\,v_{\tau(t)}(s')-v_{\tau(t)}(S_{t+1})\Big)\le D(M)\sqrt{2n\log(2/\delta)},$$
--   where $v_{\tau(t)}$ is the bias of the optimistic plan of the phase current at time $t$.
--
--   Each summand is the difference between the conditional expectation of $v_{\tau(t)}(S_{t+1})$ given the past and its realisation, so the partial sums form a martingale; the bias is measurable with respect to the history at the start of its phase, and on the good event its span is at most $D(M)$, so the increments lie in an interval of length $D(M)$ and the Azuma--Hoeffding inequality gives the bound with probability $1-\delta/2$. That the span bound is only available on the good event is handled by stopping the martingale when the good event first fails, which changes nothing on the good event and keeps the increments bounded everywhere.
--
--   **Formalization Note** The last round is excluded because the state $S_n$ following it is not recorded by a trajectory of $n$ rounds; the corresponding increment is discharged separately by choosing $S_n$ to maximise the bias of the last phase, which makes it nonpositive.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Section 38.6 Step 4 (the martingale term of the regret decomposition) together with the Azuma-Hoeffding inequality of Section 5.2, printed pp. 527-528 and p. 71 / PDF pp. 536-537 and p. 80; Jaksch, Ortner and Auer, JMLR 11 (2010), Section 4.3.

import Definitions.Def_UCRL2Algorithm

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_ucrl2_bias_martingale_deviation
    (S A n : ℕ) [NeZero A] (hS : 2 ≤ S) (hn : 0 < n)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (r : Fin S → Fin A → ℝ) (hr : ∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1)
    (M : FiniteMDP S A) (hMr : M.r = r) (hD : 1 ≤ mdpDiameter M)
    (μ0 : MDPStateDistribution S) :
    ∃ E : Set (MDPTrajectory S A n),
      mdpMeasure M μ0 (ucrl2Policy n δ r) n Eᶜ ≤ ENNReal.ofReal (δ / 2) ∧
      ∀ h ∈ mdpConfidenceGoodEvent M n δ ∩ E,
      ∀ (st : ℕ → Fin S) (act : ℕ → Fin A), (∀ t : Fin n, h t = (st t, act t)) →
        ∑ t ∈ Finset.range (n - 1),
            ((∑ s', (M.P (st t) (act t) s' : ℝ)
                * mdpOptimisticBias r
                    (fun x a ↦ mdpConfidenceSet h (mdpPhaseStart h t + 1) n δ x a) s')
              - mdpOptimisticBias r
                  (fun x a ↦ mdpConfidenceSet h (mdpPhaseStart h t + 1) n δ x a)
                  (st (t + 1)))
          ≤ mdpDiameter M * Real.sqrt (2 * n * Real.log (2 / δ)) := by
  sorry
