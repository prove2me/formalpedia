-- Prove2me | Theorems.Thm_BanditAlgorithm_jao_two_state_reference_occupancy_bounds
-- name    : BanditAlgorithm.jao_two_state_reference_occupancy_bounds
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-05T17:32:17.029293+00:00
-- url     : https://prove2.me/theorems/88c38a09-b8af-446b-9096-36c51e2cf891
-- title:
--   JAO equation (35): in the reference two-state gadget the time spent in $s_p$ is at least $\frac{T}{2} - \frac{D'}{2}$
-- statement:
--   Throughout, the MDP is the collapsed two-state gadget of JAO Figure 3, presented by its defining equations rather than through an auxiliary definition: state $0$ is $s_\circ$ with reward $0$, state $1$ is $s_p$ with reward $1$, the return probability is $p(s_\circ \mid s_p, b) = \delta$ for every action $b$, and the escape probability is $p(s_p \mid s_\circ, b) = \delta$ for every action other than the planted action $a$, for which it is $\delta + \varepsilon$. The gadget has diameter $D' = 1/\delta$. The reference MDP $M_0$ is the same gadget with no planting.
--
--   **Statement.** For $0 < \delta \le \tfrac13$, every horizon $T$ and **every** policy $\pi$ (in the reference gadget all actions have the same transition law, so the policy is irrelevant),
--   $$\mathbb{E}_{\mathrm{unif}}[N_p] \;\ge\; \frac{T}{2} - \frac{1}{2\delta}
--   \qquad\text{and}\qquad
--   \sum_{b} \mathbb{E}_{\mathrm{unif}}[N_\circ^*(b)] \;\le\; \frac{T}{2} + \frac{1}{2\delta},$$
--   where $N_p$ is the number of rounds spent in $s_p$ — equivalently the total reward — and $N_\circ^*(b)$ is the number of rounds in which action $b$ is played in state $s_\circ$.
--
--   The first inequality is equation (35) of JAO (p. 1583), with $D' = 1/\delta$. It is proved by conditioning on the step $\tau_{\circ p}$ of the first transition out of $s_\circ$, which is geometric with parameter $\delta$: given $\tau_{\circ p} = t$, the chain is symmetric from then on and spends at least $(T-t)/2$ rounds in $s_p$ in expectation, and summing $\frac{T-t}{2}(1-\delta)^{t-1}\delta$ over $t$ and evaluating the two geometric series gives $\frac{T}{2} - \frac{1}{2\delta} + \frac{(1-\delta)^T}{2\delta} \ge \frac{T}{2} - \frac{1}{2\delta}$.
--
--   The second inequality is the immediate consequence JAO record just after (37): the counts $N_\circ^*(b)$ partition the visits to $s_\circ$, so their sum is $N_\circ = T - N_p$, and the first inequality bounds its expectation. Both are stated together because they are the same computation, and the assembly needs both.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Section 6 (pp. 1583-1586): equations (34)-(37), Lemma 13 and the concluding computation. Lemma 13 is adapted from Auer, Cesa-Bianchi, Freund & Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM J. Comput. 32 (2002) 48-77, Theorem A.2 and its proof in the appendix.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_UCRL2ConfidenceSets

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.jao_two_state_reference_occupancy_bounds
    {m : ℕ} (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3)
    (M₀ : FiniteMDP 2 m)
    (hr0 : ∀ b, M₀.r 0 b = 0) (hr1 : ∀ b, M₀.r 1 b = 1)
    (hP1 : ∀ b, (M₀.P 1 b 0 : ℝ) = δ) (hP0 : ∀ b, (M₀.P 0 b 1 : ℝ) = δ)
    (T : ℕ) (π : MDPPolicy 2 m) :
    (T : ℝ) / 2 - 1 / (2 * δ)
        ≤ ∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac 0) π T)
      ∧ ∑ b : Fin m,
            (∫ h, (mdpVisitCount h T 0 b : ℝ) ∂(mdpMeasure M₀ (mdpStateDirac 0) π T))
          ≤ (T : ℝ) / 2 + 1 / (2 * δ) := by
  sorry
