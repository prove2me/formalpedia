-- Prove2me | Theorems.Thm_DeepBisimulationControl_pi_bisim_metric_fixed_point
-- name    : DeepBisimulationControl.pi_bisim_metric_fixed_point
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:03:14.955843+00:00
-- url     : https://prove2.me/theorems/218c717f-7246-467a-9687-ba0669cfe698
-- title:
--   Theorem 1 (as proved): policy iteration reaches $\pi^*$ and $\mathcal F(\cdot,\pi^*)$ has a least fixed point
-- statement:
--   Let $\mathcal S$ be a finite state space, $\mathcal A$ a finite nonempty action space, $\mathcal P$ a transition kernel, $\mathcal R$ a reward function, $\gamma\in[0,1)$ and $c\in[0,1)$. Let $\sigma_0,\sigma_1,\dots$ be a run of policy iteration: $\sigma_{k+1}(s)\in\arg\max_aQ^{\sigma_k}(s,a)$, with $\sigma_{k+1}(s)=\sigma_k(s)$ whenever $\sigma_k(s)$ is a maximiser. For a policy $\pi$ let
--
--   $$F(d,\pi)(s_i,s_j)=(1-c)\,|r^\pi_{s_i}-r^\pi_{s_j}|+c\,W_1(\mathcal P^\pi_{s_i},\mathcal P^\pi_{s_j};d).$$
--
--   Then there are $K\in\mathbb N$ and a deterministic policy $\pi^*$ such that:
--   1. $\pi^*$ is optimal and $\sigma_k=\pi^*$ for all $k\ge K$;
--   2. $\tilde d=\sup_nF(\cdot,\pi^*)^n(0)$ is a pseudometric with $F(\tilde d,\pi^*)=\tilde d$;
--   3. $\tilde d\le d$ pointwise for every pseudometric $d$ with $F(d,\pi^*)=d$, so $\tilde d$ is the least fixed point of $F(\cdot,\pi^*)$ in the space of (bounded) pseudometrics;
--   4. the iterates $d_0=0$, $d_{n+1}=F(d_n,\sigma_n)$ computed along policy iteration converge pointwise to $\tilde d$.
--
--   This is the paper's statement that the $\pi^*$-bisimulation metric is the fixed point reached while the policy improves.
--
--   **Formalization Note** The printed Theorem 1 speaks of a policy that is "continuously improving" and a "$\pi^*$-bisimulation metric" without defining either. Its proof argues through policy iteration (eqs. (10)-(11)) and the existence of a fixed point of $F(\cdot,\pi)$ for a fixed $\pi$. The statement above is what that argument establishes, with "continuously improving" read as policy iteration and the $\pi^*$-bisimulation metric read as the least fixed point of $F(\cdot,\pi^*)$. The tie-breaking rule is the standard one; without it policy iteration can alternate between optimal policies forever. On a finite state space every pseudometric is bounded.
-- source:
--   Zhang, McAllister, Calandra, Gal and Levine, Learning Invariant Representations for Reinforcement Learning without Reconstruction, arXiv:2006.10742v2 (ICLR 2021), Section 5, Theorem 1, eq. (5), p. 5; proof in Appendix A, eqs. (9)-(11), p. 12

import Mathlib
import Definitions.Def_DeepBisimulationControl_Basic

open Filter Topology

namespace DeepBisimulationControl

theorem pi_bisim_metric_fixed_point {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsKernel P) (R : S → A → ℝ) (gamma c : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (sigma : ℕ → S → A) (hsigma : IsPolicyIteration P R gamma sigma) :
    ∃ (K : ℕ) (sigmaStar : S → A),
      IsOptimalPolicy P R gamma (detPolicy sigmaStar) ∧ (∀ k, K ≤ k → sigma k = sigmaStar) ∧
      IsPseudometric (piBisimMetric P R c (detPolicy sigmaStar)) ∧
      piBisimOperator P R c (detPolicy sigmaStar) (piBisimMetric P R c (detPolicy sigmaStar)) =
        piBisimMetric P R c (detPolicy sigmaStar) ∧
      (∀ d : S → S → ℝ, IsPseudometric d → piBisimOperator P R c (detPolicy sigmaStar) d = d →
        ∀ s t, piBisimMetric P R c (detPolicy sigmaStar) s t ≤ d s t) ∧
      (∀ s t, Tendsto (fun n => policyIterationMetric P R c sigma n s t) atTop
        (𝓝 (piBisimMetric P R c (detPolicy sigmaStar) s t))) := by sorry

end DeepBisimulationControl
