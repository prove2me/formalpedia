-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_ucrl2_confidence_event_complement_prob_le
-- name    : BanditAlgorithm.mdp_ucrl2_confidence_event_complement_prob_le
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T20:41:48.081506+00:00
-- url     : https://prove2.me/theorems/72e0eb0b-4081-4069-a50e-f908dc2892a2
-- title:
--   The UCRL2 confidence sets fail with probability at most $\delta/2$
-- statement:
--   For every finite MDP $M$ with $S\ge2$ states and $A\ge1$ actions, every horizon $n\ge1$, every confidence level $\delta\in(0,1)$, **every policy** and every initial state distribution,
--   $$\mathbb P\bigl(\text{some true transition row leaves its confidence ball}\bigr)\le\frac{\delta}{2},$$
--   that is, the complement of `mdpConfidenceGoodEvent` has probability at most $\delta/2$.
--
--   This is the statistical content of the analysis of UCRL2 (Lattimore--Szepesvari, Section 38.6, Step 1; Lemma 38.8), and it is a statement about the estimates alone -- it holds uniformly over policies, because the confidence balls are built from the trajectory and no property of the action-selection rule enters.
--
--   The argument is a union bound over the state-action pairs, over the possible values $m\le n$ of the number of observations, and over the $2^{S}$ events of the categorical concentration inequality: conditionally on having been played $m$ times, the empirical row of a pair is the empirical distribution of $m$ independent draws from the true row, so it deviates by $\varepsilon$ in $\ell^1$ with probability at most $2^{S}e^{-m\varepsilon^{2}/2}$; at $\varepsilon$ equal to the confidence radius this is $2^{S}(\delta/2SAn)^{7S}$, and the slack in $7S$ absorbs the union.
--
--   **Formalization Note** The subtlety the statement hides, and the reason it is not a direct application of the fixed-sample-size inequality, is that the number of observations of a pair is itself random -- a stopping time -- so the concentration must be applied along the peeling over $m$ rather than to a fixed sample.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Section 38.6 Step 1 and Lemma 38.8 (Exercise 38.21), printed pp. 525-527 / PDF pp. 534-536; after Jaksch, Ortner and Auer, Near-optimal regret bounds for reinforcement learning, JMLR 11 (2010), Section 4.1 and Appendix C.1.

import Definitions.Def_UCRL2ConfidenceSets

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.mdp_ucrl2_confidence_event_complement_prob_le
    (S A n : ℕ) (hS : 2 ≤ S) (hA : 0 < A) (hn : 0 < n)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (M : FiniteMDP S A) (π : MDPPolicy S A) (μ0 : MDPStateDistribution S) :
    mdpMeasure M μ0 π n (mdpConfidenceGoodEvent M n δ)ᶜ ≤ ENNReal.ofReal (δ / 2) := by
  sorry
