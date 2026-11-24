-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_Supplement_lemma_6
-- name    : AvgRewardPMD.SPMD.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:26:27.975072+00:00
-- url     : https://prove2.me/theorems/1019bbf5-aefe-468c-90aa-4949b3881ef4
-- title:
--   Lemma 6, p. 13 — E[(ρ(π_{k+1})−ρ(π*))/(1−Γ) + (1/λ_k+ω)D(π_{k+1},π*)] ≤ E[Γ(ρ(π_k)−ρ(π*))/(1−Γ) + D(π_k,π*)/λ_k] + ς + λ_kσ²/(8(1−Γ))
-- statement:
--   Let $\mathcal M=(\mathcal S,\mathcal A,\mathsf P,c)$ be a finite AMDP satisfying the mixing Assumption 1 and the ergodicity Assumption 2, and let $\Gamma\in(0,1)$ satisfy $\min_s\nu^\pi(s)\ge1-\Gamma$ for every feasible policy $\pi$. Let the regularizer $h^\pi(s)=h_s(\pi(\cdot\mid s))$ be convex with modulus $\omega>0$ in the sense of (2.2), and let $\rho(\pi)$, $\bar Q^\pi$ be the average cost and the basic differential Q-function of the regularized cost $c(s,a)+h^\pi(s)$. Let $\pi^*$ be a feasible policy with stationary distribution $\nu^*$ and $D(\pi,\pi')=\mathbb E_{s\sim\nu^*}[D^{\pi'}_\pi(s)]$.
--
--   Fix $k\ge0$ and run SPMD (Algorithm 1) on a probability space with stepsizes $\lambda_j>0$ for $j\le k$, the critic outputs $\bar{\mathcal Q}^{\pi_j,\zeta_j}$, $j\le k$, satisfying Assumption 3: (3.7) and (3.9) with constants $\varsigma,\kappa$ and (3.8) with constant $\sigma$. Then
--   $$\mathbb E\Big[\frac{1}{1-\Gamma}\big(\rho(\pi_{k+1})-\rho(\pi^*)\big)+\Big(\frac1{\lambda_k}+\omega\Big)D(\pi_{k+1},\pi^*)\Big]\le\mathbb E\Big[\frac{\Gamma}{1-\Gamma}\big(\rho(\pi_k)-\rho(\pi^*)\big)+\frac1{\lambda_k}D(\pi_k,\pi^*)\Big]+\varsigma+\frac{\lambda_k\sigma^2}{8(1-\Gamma)},$$
--   where the expectation is the full expectation over the run.
--
--   This is the recursion that drives the linear convergence analysis of Theorem 3: the gap contracts by the factor $\Gamma$ and the distance by $1/(1+\lambda_k\omega)$, with the bias entering additively and the variance multiplied by the stepsize.
--
--   **Formalization Note** Expectations are Bochner integrals. The average costs $\rho(\pi_j)$ and the distances $D(\pi_j,\pi^*)$ for $j\in\{k,k+1\}$ are assumed integrable, since the lemma writes their expectations.
--
--   Differences from the source:
--   - generalization: π*, an optimal policy of (2.5) → any feasible policy π⋆ with a stationary distribution ν⋆; reason: the inequality uses Lemma 2 and the three-point inequality, never optimality; an optimal policy is an instance (as in the published Lemma 4)
--   - generalization: stepsizes λ_k > 0 at every step → λ_j > 0 for j ≤ k only; reason: steps after k do not enter the inequality at step k; positive stepsizes at every step are an instance
--   - generalization: Assumption 3 for every k ≥ 0 → Assumption 3 ((3.7), (3.8), (3.9)) for the critic outputs j ≤ k, π_j ℱ j-measurable for j ≤ k + 1; reason: later steps do not enter the inequality at step k
--   - generalization: F_s = σ(ζ_0, …, ζ_s) → any filtration ℱ to which the iterates are adapted (π_k is ℱ k-measurable); reason: the natural filtration is an instance; this is the published CriticAssumption convention
--   - encoding: E_{ζ_k}, the expectation given F_{k−1} → the conditional expectation given ℱ k; reason: index shift by one, ℱ k plays F_{k−1}, as in the published CriticAssumption
--   - encoding: the expectations written in the lemma and in Assumption 3 → integrability of ρ(π_j) and D(π_j, π⋆) for j ≤ k + 1, of every entry of Q̂_j, of ‖Q̂_j‖²_sp and of ‖δ_j‖²_sp; reason: the source writes these expectations, so they are finite there
--   - encoding: the expectation taken with respect to F_{−1} → the integral over the probability space; reason: F_{−1} is the trivial σ-field, so the expectation is the full expectation
--   - generalization: h^π closed convex → h convex with (2.2) at strictly positive points; closedness not assumed; reason: the statement concerns strictly positive iterates and (2.2) there; a closed convex regularizer is an instance
--   - reading: (2.2) for π′ ranging over all policies → (2.2) at strictly positive π′ only (the published IsKLStrongConvex); reason: at a boundary π′ with ω > 0 no finite h satisfies (2.2); every SPMD iterate is strictly positive; this is the convention of the published base mission
--   - encoding: ρ(π), a scalar → ρ^π(s₀) = avgCost at an arbitrary start state s₀; reason: under Assumption 1 the average cost does not depend on the start state (§2.1, p. 6), as in the published base items
--   - generalization: κ ≥ 0 in Assumption 3 → κ : ℝ appearing only through κ²; reason: replacing κ by |κ| leaves every hypothesis and conclusion unchanged; every source κ is included
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 13, Lemma 6; proof pp. 13–14 (via Lemma 5, Lemma 2 and (3.13))

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting
import Definitions.Def_AvgRewardPMD_SPMD_Supplement_Actor

namespace AvgRewardPMD.SPMD.Supplement

open FoundationsML.ReinforcementLearning MeasureTheory

theorem lemma_6 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P) (herg : IsErgodic P)
    (c : S → A → ℝ) (h : S → (A → ℝ) → ℝ) (ω : ℝ) (hω : 0 < ω)
    (hconv : IsKLStrongConvex h ω) (Γ : ℝ) (hΓ : IsGammaBound P Γ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) (νstar : S → ℝ)
    (hνstar : MarkovMixing.IsStationary (stateMatrix P πstar) νstar)
    {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (Qhat : ℕ → Ω → S × A → ℝ) (π : ℕ → Ω → S → A → ℝ)
    (lam : ℕ → ℝ) (bias σ κ : ℝ) (hiter : IsSPMDIterates h lam Qhat π) (k : ℕ)
    (hlam : ∀ j ≤ k, 0 < lam j)
    (hcrit : CriticAssumption μ ℱ (fun π' => diffQ P π' (fun s a => c s a + h s (π' s)))
      Qhat π bias κ (k + 1))
    (hvar : CriticVariance μ ℱ (fun π' => diffQ P π' (fun s a => c s a + h s (π' s)))
      Qhat π σ (k + 1))
    (s₀ : S)
    (hintρ : ∀ j ≤ k + 1, Integrable
      (fun ξ => avgCost P (π j ξ) (fun s a => c s a + h s (π j ξ s)) s₀) μ)
    (hintD : ∀ j ≤ k + 1, Integrable (fun ξ => stationaryKL νstar (π j ξ) πstar) μ) :
    ∫ ξ, ((avgCost P (π (k + 1) ξ) (fun s a => c s a + h s (π (k + 1) ξ s)) s₀
            - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀) / (1 - Γ)
          + (1 / lam k + ω) * stationaryKL νstar (π (k + 1) ξ) πstar) ∂μ
      ≤ ∫ ξ, (Γ * (avgCost P (π k ξ) (fun s a => c s a + h s (π k ξ s)) s₀
              - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀) / (1 - Γ)
            + stationaryKL νstar (π k ξ) πstar / lam k) ∂μ
          + bias + lam k * σ ^ 2 / (8 * (1 - Γ)) := by sorry

end AvgRewardPMD.SPMD.Supplement
