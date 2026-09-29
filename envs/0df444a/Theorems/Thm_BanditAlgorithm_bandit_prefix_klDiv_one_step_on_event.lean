-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_prefix_klDiv_one_step_on_event
-- name    : BanditAlgorithm.bandit_prefix_klDiv_one_step_on_event
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T16:02:23.766625+00:00
-- url     : https://prove2.me/theorems/91399bf2-7e7c-455c-90ce-471d0142c789
-- title:
--   One-step divergence increment on an event of the past
-- statement:
--   One round of interaction adds at most one round's worth of information, even after restricting to an event decided by the past.
--
--   Fix a $k$-armed policy $\pi$ and run it in two bandit environments $\nu=(P_i)_{i=1}^k$ and $\nu'=(P_i')_{i=1}^k$, writing $\mathbb P_{\nu\pi}$ and $\mathbb P_{\nu'\pi}$ for the two laws of the infinite interaction trajectory, and $\mathcal F_t=\sigma(A_1,X_1,\dots,A_t,X_t)$ for the natural filtration. Let $E\in\mathcal F_n$ be any event decided by the first $n$ rounds. Then
--
--   $$
--   D\Big(\mathbb P_{\nu\pi}\big|_{\mathcal F_{n+1}}\!\restriction_E \,\Big\|\, \mathbb P_{\nu'\pi}\big|_{\mathcal F_{n+1}}\!\restriction_E\Big)
--   \;\le\;
--   D\Big(\mathbb P_{\nu\pi}\big|_{\mathcal F_{n}}\!\restriction_E \,\Big\|\, \mathbb P_{\nu'\pi}\big|_{\mathcal F_{n}}\!\restriction_E\Big)
--   \;+\;\sum_{i=1}^{k}\mathbb P_{\nu\pi}\big(E\cap\{A_{n+1}=i\}\big)\,D(P_i,P_i'),
--   $$
--
--   where $\restriction_E$ denotes restriction of the measure to $E$.
--
--   Only the *reward* divergences appear on the right: the policy is the same in both environments, so the policy factors cancel from the likelihood ratio, and the single new observation in round $n+1$ contributes $D(P_i,P_i')$ weighted by the probability that arm $i$ is the one played, on the part of the space selected by $E$.
--
--   Localising to an $\mathcal F_n$-event is what makes this usable inside a stopping-time argument: taking $E=\{\tau>n\}$ isolates the rounds on which the learner has not yet stopped, and summing the resulting increments over $n$ produces the expected number of pulls $\mathbb E_\nu[T_i(\tau)]$ in place of the horizon.
--
--   **Formalization Note** Trajectory coordinate $t$ is round $t+1$, so the arm played in round $n+1$ is the first component of coordinate $n$. The restriction of a probability measure to $E$ is a sub-probability measure, so the two divergences are those of finite measures.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf : Lemma 15.1 and Eq. (15.2), printed pp. 198-199 (the one-round likelihood-ratio computation in the canonical bandit model, where the policy factors cancel), localised to an event of the past as required by the stopped chain rule of Exercise 14.13, printed p. 197.

import Definitions.Def_BanditTrajectory

open MeasureTheory ProbabilityTheory InformationTheory ENNReal

theorem BanditAlgorithm.bandit_prefix_klDiv_one_step_on_event {k : ℕ}
    (ν ν' : BanditAlgorithm.StochasticBandit k) (π : BanditAlgorithm.BanditPolicy k) (n : ℕ)
    (E : Set (ℕ → Fin k × ℝ))
    (hE : MeasurableSet[BanditAlgorithm.banditFiltration k n] E) :
    @klDiv (ℕ → Fin k × ℝ) (BanditAlgorithm.banditFiltration k (n + 1))
        (((BanditAlgorithm.banditTrajMeasure ν π).trim
          ((BanditAlgorithm.banditFiltration k).le (n + 1))).restrict E)
        (((BanditAlgorithm.banditTrajMeasure ν' π).trim
          ((BanditAlgorithm.banditFiltration k).le (n + 1))).restrict E) ≤
      @klDiv (ℕ → Fin k × ℝ) (BanditAlgorithm.banditFiltration k n)
          (((BanditAlgorithm.banditTrajMeasure ν π).trim
            ((BanditAlgorithm.banditFiltration k).le n)).restrict E)
          (((BanditAlgorithm.banditTrajMeasure ν' π).trim
            ((BanditAlgorithm.banditFiltration k).le n)).restrict E) +
        ∑ i, (BanditAlgorithm.banditTrajMeasure ν π) (E ∩ {ω | (ω n).1 = i}) *
          klDiv (ν.P i) (ν'.P i) := by
  sorry
