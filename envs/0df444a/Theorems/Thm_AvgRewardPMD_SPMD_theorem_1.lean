-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_theorem_1
-- name    : AvgRewardPMD.SPMD.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:09.929725+00:00
-- url     : https://prove2.me/theorems/6b1cf188-8988-4921-8641-03402a30d320
-- title:
--   Theorem 1, p. 11 — SPMD on a mixing AMDP: E[Σ_{k<K}(ρ(π_k) − ρ(π*))] ≤ κ√(K log|A|) + Kς and E[ρ(π_r) − ρ(π*)] ≤ κ√(log|A|)/√K + ς
-- statement:
--   Let $\mathcal M=(\mathcal S,\mathcal A,\mathsf P,c)$ be a finite AMDP satisfying the mixing Assumption 1, with no regularizer ($\omega=0$, $L=0$), and let $\pi^*$ be a feasible policy. Run SPMD (Algorithm 1) on a probability space with the constant stepsize
--   $$\lambda_k=\lambda=\frac{2\sqrt{\log|\mathcal A|}}{\kappa\sqrt K},\qquad K\ge1,\ \kappa>0,$$
--   where the critic outputs $\bar{\mathcal Q}^{\pi_k,\zeta_k}$ satisfy (3.7) and (3.9) of Assumption 3 with constants $\varsigma$ and $\kappa$. Then
--
--   1. the expected cumulative optimality gap is bounded:
--   $$\mathbb E\Big[\sum_{k=0}^{K-1}\big(\rho(\pi_k)-\rho(\pi^*)\big)\Big]\le\kappa\sqrt{K\log|\mathcal A|}+K\varsigma;\qquad(3.14)$$
--   2. if $r$ is drawn uniformly from $\{0,1,\dots,K-1\}$, independently of the run,
--   $$\mathbb E\big[\rho(\pi_r)-\rho(\pi^*)\big]\le\frac{\kappa\sqrt{\log|\mathcal A|}}{\sqrt K}+\varsigma.\qquad(3.15)$$
--
--   This is the paper's convergence guarantee for the actor in unregularized AMDPs: an $\mathcal O(1/\sqrt K)$ rate up to the critic's bias $\varsigma$, with no dependence on the mixing time beyond what the critic constants carry.
--
--   **Formalization Note** "No regularizer": $L=0$ forces $h^\pi(s)$ to be independent of $\pi$, and such an $h(s)$ is absorbed into the arbitrary cost; the prox step (3.6) is run with $h=0$. $\rho(\pi)$ is the average cost from an arbitrary start state $s_0$. The iterates form an infinite sequence satisfying (3.6) at every $k$; Assumption 3 is required for the critic outputs $k<K$ and adaptedness for $k\le K$. $r$ is a measurable $\mathbb N$-valued random variable with $\mathbb P(r=i)=1/K$ for $i<K$, independent of the sequence of iterates.
--
--   Differences from the source:
--   - generalization: π*, an optimal policy → any feasible policy π⋆; reason: no step of the proof uses optimality; an optimal policy is an instance
--   - generalization: Assumption 3 with (3.7), (3.8), (3.9) → (3.7) and (3.9) only; reason: the bound does not involve σ; Assumption 3 implies the hypotheses used
--   - generalization: F_s = σ(ζ_0, …, ζ_s) → any filtration ℱ to which the iterates are adapted (π_k is ℱ k-measurable); reason: the natural filtration is an instance
--   - encoding: ω = 0, L = 0 → no regularizer (h = 0) and an arbitrary cost c; reason: L = 0 makes h^π(s) = h(s) independent of π, which is absorbed into the cost c(s,a) + h(s); the cost-only statement is exactly the printed case
--   - encoding: λ = 2√(log|A|)/(κ√K) and r uniform on {0, …, K−1} → hypotheses κ > 0 and K ≥ 1; reason: the printed stepsize divides by κ and √K and the uniform law on {0, …, K−1} needs K ≥ 1; they only exclude undefined cases
--   - encoding: E_{ζ_k}, the expectation given F_{k−1} → the conditional expectation given ℱ k; reason: index shift by one, ℱ k plays F_{k−1}
--   - encoding: the expectations written in Assumption 3 → integrability of every entry of Q̂_k and of ‖Q̂_k‖²_sp; reason: Q̃^{π_k} = E_{ζ_k}[Q̂_k] and E_{ζ_k}‖Q̂_k‖²_sp are written, so they are defined and finite in the source
--   - generalization: Algorithm 1 run for k = 0, …, K, with Assumption 3 for every k → an infinite sequence of iterates satisfying (3.6) at every k, with Assumption 3 required only for the critic outputs k < K (and π_k ℱ k-measurable for k ≤ K); reason: any run up to K extends to an infinite sequence, since the prox step always has a minimizer and later critic outputs are unconstrained; the bound involves only k < K
--   - encoding: ρ(π), a scalar → ρ^π(s_0) for an arbitrary start state s_0; reason: state independent under Assumption 1 (milestone 1)
--   - encoding: r uniformly chosen from {0, …, K−1} → r measurable, P(r = i) = 1/K for i < K, r independent of the iterate sequence; reason: the standard meaning of drawing the output index at random for the run
--   - reading: Q̄^π as the expectation of a series → the series of the expectations; reason: the pathwise series need not converge, the series of expectations converges absolutely under Assumption 1
--   - encoding: ς ≥ 0 (Assumption 3) → no sign hypothesis on ς; reason: ς ≥ 0 is forced by (3.7) because the span is nonnegative and μ is a probability measure; no instance changes
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 11, Theorem 1 (3.14)–(3.15); proof p. 12

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting

namespace AvgRewardPMD.SPMD

open FoundationsML.ReinforcementLearning MeasureTheory ProbabilityTheory

theorem theorem_1 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P) (c : S → A → ℝ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (Qhat : ℕ → Ω → S × A → ℝ) (π : ℕ → Ω → S → A → ℝ)
    (bias κ : ℝ) (hκ : 0 < κ) (K : ℕ) (hK : 1 ≤ K) (lam : ℝ)
    (hlam : lam = 2 * Real.sqrt (Real.log (Fintype.card A)) / (κ * Real.sqrt K))
    (hiter : IsSPMDIterates (fun _ _ => 0) (fun _ => lam) Qhat π)
    (hcrit : CriticAssumption μ ℱ (fun π' => diffQ P π' c) Qhat π bias κ K) (s₀ : S) :
    (∫ ξ, ∑ k ∈ Finset.range K, (avgCost P (π k ξ) c s₀ - avgCost P πstar c s₀) ∂μ
        ≤ κ * Real.sqrt (K * Real.log (Fintype.card A)) + K * bias) ∧
    (∀ r : Ω → ℕ, Measurable r → (∀ i < K, μ {ξ | r ξ = i} = (K : ENNReal)⁻¹) →
      IndepFun r (fun ξ k => π k ξ) μ →
      ∫ ξ, (avgCost P (π (r ξ) ξ) c s₀ - avgCost P πstar c s₀) ∂μ
        ≤ κ * Real.sqrt (Real.log (Fintype.card A)) / Real.sqrt K + bias) := by sorry

end AvgRewardPMD.SPMD
