-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_lemma_4
-- name    : AvgRewardPMD.SPMD.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:09.182842+00:00
-- url     : https://prove2.me/theorems/8e20d802-fb56-4b64-b491-3ef0e9370c74
-- title:
--   Lemma 4, p. 10 (corrected: λ_k multiplies only the gap) — E[λ_k(ρ(π_k) − ρ(π*)) + (1+λ_kω)D(π_{k+1},π*)] ≤ E[D(π_k,π*)] + λ_kς + λ_k²(κ²/4 + L²)
-- statement:
--   Let $\mathcal M=(\mathcal S,\mathcal A,\mathsf P,c)$ be a finite AMDP satisfying the mixing Assumption 1. Let the regularizer $h^\pi(s)=h_s(\pi(\cdot\mid s))$ be convex with modulus $\omega\ge0$ in the sense of (2.2) and $L$-Lipschitz in the $\ell_1$ norm, and let $\rho(\pi)$ and $\bar Q^\pi$ be the average cost and the basic differential Q-function of the regularized cost $c(s,a)+h^\pi(s)$. Let $\pi^*$ be a feasible policy with stationary distribution $\nu^*$, and $D(\pi,\pi')=\mathbb E_{s\sim\nu^*}[D^{\pi'}_\pi(s)]$.
--
--   Fix $k\ge0$. Run SPMD (Algorithm 1) on a probability space with stepsizes $\lambda_j\ge0$ for $j\le k$, the critic outputs $\bar{\mathcal Q}^{\pi_j,\zeta_j}$, $j\le k$, satisfying (3.7) and (3.9) of Assumption 3 for $\bar Q^{\pi_j}$. Then
--   $$\mathbb E\Big[\lambda_k\big(\rho(\pi_k)-\rho(\pi^*)\big)+(1+\lambda_k\omega)D(\pi_{k+1},\pi^*)\Big]\le\mathbb E[D(\pi_k,\pi^*)]+\lambda_k\varsigma+\lambda_k^2\Big(\frac{\kappa^2}{4}+L^2\Big).$$
--
--   This is the one-step progress inequality of SPMD: the expected gap at step $k$, weighted by the stepsize, is paid for by the decrease of the expected KL distance to the comparator, up to the bias $\varsigma$ and a second-order term in the stepsize. Summing it over $k$ gives Theorem 1 (for $\omega=0$, $L=0$) and Theorem 2.
--
--   **Formalization Note** Expectations are Bochner integrals over the probability space; the integrands are integrable under the hypotheses (the KL distances by induction from $D(\pi_0,\pi^*)\le\log|\mathcal A|$), so no integral takes a default value. $\rho$ is evaluated at an arbitrary start state. $\mathcal F_{k-1}$ of the paper is `ℱ k`.
--
--   Differences from the source:
--   - correction: E[λ_k(ρ(π_k) − ρ(π*) + (1 + λ_kω)D(π_{k+1},π*))], the stepsize multiplying the distance term too → E[λ_k(ρ(π_k) − ρ(π*)) + (1 + λ_kω)D(π_{k+1},π*)]; reason: the printed form is false: one state, two actions, c = (0, 0.01), h = 0 (ω = L = 0), exact critic Q̂_0 = Q̄^{π_0} = (−0.005, 0.005) (ς = 0, κ = 0.01), π* = (1, 0), λ_0 = 100 give a printed left side 100·(0.005 + 0.3133) = 31.83 against a right side log 2 + 0.25 = 0.943; the corrected form (0.813 ≤ 0.943) is what averaging the per-state inequality of the proof (p. 11, the display before "By taking expectation with respect to ν*") over ν* gives, and the inequality the proof of Theorem 1 telescopes (p. 12, first display); the proof's final display repeats the printed bracketing
--   - generalization: π*, an optimal policy → any feasible policy π⋆ with a stationary distribution ν⋆; reason: the proof uses no optimality; an optimal policy is an instance
--   - generalization: Assumption 3 with (3.7), (3.8), (3.9) → (3.7) and (3.9) only; reason: the bound does not involve σ; Assumption 3 implies the hypotheses used
--   - generalization: stepsizes λ_k (positive), Assumption 3 for every k ≥ 0 → λ_j ≥ 0 for j ≤ k, Assumption 3 for the critic outputs j ≤ k only and π_j ℱ j-measurable for j ≤ k + 1; reason: positive stepsizes and the assumption at every step are an instance; later steps do not enter the inequality at step k
--   - generalization: F_s = σ(ζ_0, …, ζ_s) → any filtration ℱ to which the iterates are adapted (π_k is ℱ k-measurable); reason: π_k is a function of ζ_0, …, ζ_{k−1}, so the natural filtration is an instance
--   - encoding: E_{ζ_k}, the expectation given F_{k−1} → the conditional expectation given ℱ k; reason: index shift by one, ℱ k plays F_{k−1}
--   - encoding: the expectations written in Assumption 3 → integrability of every entry of Q̂_k and of ‖Q̂_k‖²_sp; reason: Q̃^{π_k} = E_{ζ_k}[Q̂_k] and E_{ζ_k}‖Q̂_k‖²_sp are written, so these are defined and finite in the source
--   - encoding: h^π closed convex and L-Lipschitz → h convex and L-Lipschitz, closedness not assumed; reason: a Lipschitz convex function is continuous, hence closed, so no instance changes
--   - reading: h^π is L-Lipschitz (norm unspecified) → |h_s(p) − h_s(p′)| ≤ L‖p − p′‖_1; reason: the proof's step (i) uses the ℓ_1 norm; it is the weakest of the usual choices as a hypothesis
--   - reading: (2.2) for π′ ranging over all policies → (2.2) at strictly positive π′ only; reason: at a boundary π′ with ω > 0 no finite h satisfies (2.2), not even the paper's example ωD^π_{π_0}; every SPMD iterate is strictly positive
--   - encoding: ρ(π), a scalar → ρ^π(s_0) for an arbitrary start state s_0; reason: state independent under Assumption 1 (milestone 1)
--   - reading: Q̄^π as the expectation of a series → the series of the expectations; reason: the pathwise series need not converge, the series of expectations converges absolutely under Assumption 1
--   - encoding: ς, κ ≥ 0 (Assumption 3) → no sign hypothesis on ς and κ; reason: κ enters only through κ², so κ and |κ| give the same statement, and ς ≥ 0 is forced by (3.7) because the span is nonnegative and μ is a probability measure; no instance changes
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 10, Lemma 4 (3.12); proof pp. 10–11

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting

namespace AvgRewardPMD.SPMD

open FoundationsML.ReinforcementLearning MeasureTheory

theorem lemma_4 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P)
    (c : S → A → ℝ) (h : S → (A → ℝ) → ℝ) (ω L : ℝ)
    (hconv : IsKLStrongConvex h ω) (hLip : IsL1Lipschitz h L)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) (νstar : S → ℝ)
    (hνstar : MarkovMixing.IsStationary (stateMatrix P πstar) νstar)
    {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (Qhat : ℕ → Ω → S × A → ℝ) (π : ℕ → Ω → S → A → ℝ)
    (lam : ℕ → ℝ) (k : ℕ) (hlam : ∀ j ≤ k, 0 ≤ lam j) (bias κ : ℝ)
    (hiter : IsSPMDIterates h lam Qhat π)
    (hcrit : CriticAssumption μ ℱ (fun π' => diffQ P π' (fun s a => c s a + h s (π' s)))
      Qhat π bias κ (k + 1))
    (s₀ : S) :
    ∫ ξ, (lam k * (avgCost P (π k ξ) (fun s a => c s a + h s (π k ξ s)) s₀
            - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀)
          + (1 + lam k * ω) * stationaryKL νstar (π (k + 1) ξ) πstar) ∂μ
      ≤ ∫ ξ, stationaryKL νstar (π k ξ) πstar ∂μ + lam k * bias
          + lam k ^ 2 * (κ ^ 2 / 4 + L ^ 2) := by sorry

end AvgRewardPMD.SPMD
