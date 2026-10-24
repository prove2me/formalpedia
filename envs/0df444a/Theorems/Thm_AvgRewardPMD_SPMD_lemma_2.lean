-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_lemma_2
-- name    : AvgRewardPMD.SPMD.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:11.423989+00:00
-- url     : https://prove2.me/theorems/7431ff2e-28c2-4357-a950-f9228c7c61e7
-- title:
--   Lemma 2, p. 7 — performance difference: ρ(π′) − ρ(π) = E_{s∼ν^{π′}}[⟨Q̄^π(s,·), π′(·|s) − π(·|s)⟩ + h^{π′}(s) − h^π(s)]
-- statement:
--   Let $\mathcal M=(\mathcal S,\mathcal A,\mathsf P,c)$ be a finite AMDP satisfying the mixing Assumption 1 and let $h:\mathcal S\times\Delta_{|\mathcal A|}\to\mathbb R$ be a regularizer, $h^\pi(s)=h_s(\pi(\cdot\mid s))$. For a policy $\pi$ write $\rho(\pi)$ and $\bar Q^\pi$ for the average cost and the basic differential Q-function of the regularized cost $c(s,a)+h^\pi(s)$. Then for any two feasible policies $\pi,\pi'$, with $\nu^{\pi'}$ the stationary distribution of $P_{\pi'}$,
--   $$\rho(\pi')-\rho(\pi)=\mathbb E_{s\sim\nu^{\pi'}}\Big[\big\langle\bar Q^\pi(s,\cdot),\pi'(\cdot\mid s)-\pi(\cdot\mid s)\big\rangle+h^{\pi'}(s)-h^\pi(s)\Big].\qquad(3.2)$$
--
--   This is the average-reward performance difference lemma. It turns the optimality gap $\rho(\pi)-\rho(\pi^*)$ into an expectation over the comparator's stationary distribution of a linear term in the policy, which is what the policy mirror descent analysis (Lemma 4) controls step by step.
--
--   **Formalization Note** $\rho$ is evaluated at an arbitrary start state $s_0$; it does not depend on it under Assumption 1. $\nu^{\pi'}$ is any stationary distribution of $P_{\pi'}$ (unique under Assumption 1).
--
--   Differences from the source:
--   - generalization: h^π a closed convex function of the policy satisfying (2.2) → any real function h_s(π(·|s)) of the state and of the policy at that state; reason: the identity uses no convexity; a regularizer satisfying (2.2) is an instance
--   - encoding: ρ(π), a scalar → ρ^π(s_0) for an arbitrary start state s_0; reason: ρ^π(s) does not depend on s under Assumption 1 (milestone 1)
--   - encoding: ν^{π′}, the stationary distribution → any stationary distribution ν′ of P_{π′}; reason: unique under Assumption 1
--   - reading: Q̄^π as the expectation of the series of c(s_t,a_t) + h^π(s_t) − ρ^π → the series of the expectations; reason: the pathwise series need not converge, the series of expectations converges absolutely under Assumption 1
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 7, Lemma 2 (3.2)

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting

namespace AvgRewardPMD.SPMD

open FoundationsML.ReinforcementLearning

theorem lemma_2 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P)
    (c : S → A → ℝ) (h : S → (A → ℝ) → ℝ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (ν' : S → ℝ)
    (hν' : MarkovMixing.IsStationary (stateMatrix P π') ν') (s₀ : S) :
    avgCost P π' (fun s a => c s a + h s (π' s)) s₀ - avgCost P π (fun s a => c s a + h s (π s)) s₀
      = ∑ s, ν' s * (∑ a, diffQ P π (fun s a => c s a + h s (π s)) (s, a) * (π' s a - π s a)
          + h s (π' s) - h s (π s)) := by sorry

end AvgRewardPMD.SPMD
