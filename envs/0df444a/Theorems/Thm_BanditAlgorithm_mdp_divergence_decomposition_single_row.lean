-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_divergence_decomposition_single_row
-- name    : BanditAlgorithm.mdp_divergence_decomposition_single_row
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-04T04:16:27.974686+00:00
-- url     : https://prove2.me/theorems/a6077e35-485e-43ef-9dd0-8bdf73f10418
-- title:
--   Divergence decomposition for two MDPs differing in a single transition row
-- statement:
--   **The divergence decomposition for Markov decision processes** (Lattimore--Szepesv\'ari, *Bandit Algorithms*, eq. 38.22; Exercise 38.30).
--
--   Let $M_0$ and $M_1$ be finite Markov decision processes on the same state and action spaces which agree in every transition row except one, say the row at the pair $(s_\star,a_\star)$.  Fix an initial state distribution $\mu_0$ and a history-dependent policy $\pi$, and let $\mathbb P_0^n,\mathbb P_1^n$ be the laws of the $n$-round trajectory $(S_1,A_1),\dots,(S_n,A_n)$ under the two processes.  Then the relative entropy between the two trajectory laws factorises exactly:
--   $$D\big(\mathbb P_0^n\,\|\,\mathbb P_1^n\big)=\mathbb E_0\big[N_{n-1}(s_\star,a_\star)\big]\cdot D\big(P_0(\cdot\mid s_\star,a_\star)\,\|\,P_1(\cdot\mid s_\star,a_\star)\big),$$
--   where $N_k(s,a)$ counts the rounds strictly before time $k$ at which the pair $(s,a)$ was played.
--
--   The count is $N_{n-1}$, not $N_n$: divergence accrues only at rounds whose successor state is actually recorded in the trajectory, and the state following the last recorded round has not been observed.  The identity holds for **every** history-dependent policy, which is what makes it usable in minimax lower bounds: the policy contributes nothing to the divergence, because it sees the same history under both processes.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf, eq. (38.22) (printed p. 531, PDF p. 540) and Exercise 38.30 (printed p. 536); cf. Jaksch, Ortner and Auer, JMLR 11 (2010) 1563-1600, Lemma 13 and Appendix E.

import Definitions.Def_UCRL2ConfidenceSets
import Mathlib.InformationTheory.KullbackLeibler.ChainRule

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

theorem BanditAlgorithm.mdp_divergence_decomposition_single_row {S A : ℕ}
    {M₀ M₁ : FiniteMDP S A} {μ0 : MDPStateDistribution S} {π : MDPPolicy S A}
    {sStar : Fin S} {aStar : Fin A}
    (hrow : ∀ (s : Fin S) (a : Fin A), (s, a) ≠ (sStar, aStar) → M₀.P s a = M₁.P s a)
    (hac : (M₀.transitionDist sStar aStar).toMeasure
      ≪ (M₁.transitionDist sStar aStar).toMeasure) (n : ℕ) :
    klDiv (mdpMeasure M₀ μ0 π n) (mdpMeasure M₁ μ0 π n)
      = (∫⁻ h, (mdpVisitCount h (n - 1) sStar aStar : ℝ≥0∞) ∂(mdpMeasure M₀ μ0 π n))
        * klDiv (M₀.transitionDist sStar aStar).toMeasure
            (M₁.transitionDist sStar aStar).toMeasure := by sorry
