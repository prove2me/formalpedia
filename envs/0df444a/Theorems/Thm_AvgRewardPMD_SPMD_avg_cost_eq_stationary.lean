-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_avg_cost_eq_stationary
-- name    : AvgRewardPMD.SPMD.avg_cost_eq_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:03.582296+00:00
-- url     : https://prove2.me/theorems/0c0497c1-eb99-46f8-b633-73a200596f1a
-- title:
--   §2.1, p. 6 — on a mixing AMDP the average cost is the stationary mean: ρ^π(s) = ⟨ν^π, c^π⟩ for every s
-- statement:
--   Let $\mathcal M=(\mathcal S,\mathcal A,\mathsf P,c')$ be a finite AMDP satisfying the mixing Assumption 1, let $\pi$ be a feasible policy, and let $\nu$ be a stationary distribution of $P_\pi$. Then for every start state $s$ the Cesàro means of the expected costs converge, and
--   $$\rho^\pi(s)=\lim_{T\to\infty}\frac1T\sum_{t=0}^{T-1}(P_\pi^t c'^\pi)(s)=\langle\nu,c'^\pi\rangle=\sum_{s'}\nu(s')\sum_a c'(s',a)\pi(a\mid s').$$
--
--   In particular the average cost does not depend on the start state. Taking $c'(s,a)=c(s,a)+h^\pi(s)$ gives the paper's $\rho^\pi=\langle\nu^\pi,c^\pi+h^\pi\rangle$, the scalar every later statement of the mission calls $\rho(\pi)$.
--
--   **Formalization Note** The cost is an arbitrary $c':\mathcal S\times\mathcal A\to\mathbb R$; a regularizer enters through it. The conclusion states the convergence of the Cesàro means as well as the value of `avgCost`.
--
--   Differences from the source:
--   - generalization: the cost c + h^π → any cost c′(s,a); reason: c′(s,a) = c(s,a) + h^π(s) is an instance, and then c′^π = c^π + h^π because π(·|s) sums to one
--   - encoding: ν^π, the stationary distribution → any stationary distribution ν of P_π; reason: under Assumption 1 the stationary distribution is unique, so this is the same object
--   - encoding: ρ^π(s) := lim_{T→∞} of the Cesàro means, whose existence (2.1) presupposes → the Cesàro means converge to ⟨ν, c′^π⟩, and `avgCost` (a `limUnder`) equals that value; reason: `limUnder` returns a default value when no limit exists, so the existence the source takes for granted is stated explicitly; no instance changes
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 6, §2.1, display after Assumption 1 (ρ^π(s) = ρ^π := ⟨ν^π, c^π + h^π⟩)

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting

namespace AvgRewardPMD.SPMD

open FoundationsML.ReinforcementLearning Filter Topology

theorem avg_cost_eq_stationary {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P)
    (π : S → A → ℝ) (hπ : IsPolicy π) (ν : S → ℝ)
    (hν : MarkovMixing.IsStationary (stateMatrix P π) ν) (c : S → A → ℝ) :
    ∀ s, Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
          ∑ t ∈ Finset.range T, (((stateMatrix P π) ^ t).mulVec (InducedReward π c)) s)
        atTop (𝓝 (∑ s', ν s' * InducedReward π c s')) ∧
      avgCost P π c s = ∑ s', ν s' * InducedReward π c s' := by sorry

end AvgRewardPMD.SPMD
