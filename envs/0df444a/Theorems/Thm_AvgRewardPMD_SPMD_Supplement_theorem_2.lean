-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_Supplement_theorem_2
-- name    : AvgRewardPMD.SPMD.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:25:12.282509+00:00
-- url     : https://prove2.me/theorems/80435b8b-413b-4dad-aeb1-2da80388c7dc
-- title:
--   Theorem 2, p. 12 — strongly convex L-Lipschitz regularizer, λ_k = 2/(ω(k+1)): weighted gap + ωE[D(π_K,π*)] bound and the random-output bound (3.16)
-- statement:
--   Let $\mathcal M=(\mathcal S,\mathcal A,\mathsf P,c)$ be a finite AMDP satisfying the mixing Assumption 1, and let the regularizer $h^\pi(s)=h_s(\pi(\cdot\mid s))$ be convex with modulus $\omega>0$ in the sense of (2.2) and $L$-Lipschitz in the $\ell_1$ norm. Let $\rho(\pi)$ and $\bar Q^\pi$ be the average cost and the basic differential Q-function of the regularized cost $c(s,a)+h^\pi(s)$, let $\pi^*$ be a feasible policy with stationary distribution $\nu^*$, and $D(\pi,\pi')=\mathbb E_{s\sim\nu^*}[D^{\pi'}_\pi(s)]$.
--
--   Run SPMD (Algorithm 1) from $\pi_0(a\mid s)=1/|\mathcal A|$ with the stepsizes $\lambda_k=\frac{2}{\omega(k+1)}$, the critic outputs $\bar{\mathcal Q}^{\pi_k,\zeta_k}$, $k<K$, satisfying (3.7) and (3.9) of Assumption 3 with constants $\varsigma$ and $\kappa$, for a horizon $K\ge1$. Then
--   $$\frac{1}{\sum_{k=0}^{K-1}(k+2)}\sum_{k=0}^{K-1}(k+2)\,\mathbb E[\rho(\pi_k)-\rho(\pi^*)]+\omega\,\mathbb E[D(\pi_K,\pi^*)]\le\frac{2\omega}{K(K+3)}D(\pi_0,\pi^*)+\varsigma+\frac{2\kappa^2+8L^2}{\omega(K+3)} .$$
--   Consequently, if $r$ is a random index, independent of the run, with $\Pr(r=i)=\frac{2(i+2)}{K(K+3)}$ for $i=0,\dots,K-1$, then
--   $$\mathbb E[\rho(\pi_r)-\rho(\pi^*)]\le\frac{2\omega}{K(K+3)}D(\pi_0,\pi^*)+\varsigma+\frac{2\kappa^2+8L^2}{\omega(K+3)} .\tag{3.16}$$
--
--   For strongly convex regularizers the SPMD rate improves from the $O(1/\sqrt K)$ of Theorem 1 to $O(1/K)$, up to the bias $\varsigma$ of the critic; this is the actor half of Corollary 2.
--
--   **Formalization Note** Expectations are Bochner integrals on a probability space; the random output $r$ is a measurable $\mathbb N$-valued map with the stated law, independent of the whole sequence of iterates. $D(\pi_0,\pi^*)$ is written with the uniform policy, which is $\pi_0$ on every sample point.
--
--   Differences from the source:
--   - generalization: π*, an optimal policy of (2.5) → any feasible policy π⋆ with a stationary distribution ν⋆; reason: the inequality uses Lemma 2 and the three-point inequality, never optimality; an optimal policy is an instance (as in the published Lemma 4)
--   - generalization: Assumption 3 with (3.7), (3.8), (3.9) → (3.7) and (3.9) only (the published CriticAssumption); reason: the bound does not involve σ; Assumption 3 implies the hypotheses used
--   - generalization: F_s = σ(ζ_0, …, ζ_s) → any filtration ℱ to which the iterates are adapted (π_k is ℱ k-measurable); reason: the natural filtration is an instance; this is the published CriticAssumption convention
--   - encoding: E_{ζ_k}, the expectation given F_{k−1} → the conditional expectation given ℱ k; reason: index shift by one, ℱ k plays F_{k−1}, as in the published CriticAssumption
--   - encoding: the expectations written in Assumption 3 → integrability of every entry of Q̂_k and of ‖Q̂_k‖²_sp (inside CriticAssumption); reason: those expectations are written in the source, so they are finite there
--   - reading: λ_k = λ = 2/(ω(k+1)) → the k-dependent schedule λ_k = 2/(ω(k+1)); reason: the printed "= λ" is a leftover from Theorem 1; the formula depends on k and the proof uses λ_k = 2/(ω(k+1))
--   - reading: h^π is L-Lipschitz (norm unspecified) → |h_s(p) − h_s(p′)| ≤ L‖p − p′‖_1 (published IsL1Lipschitz); reason: the proof of Lemma 4 uses the ℓ_1 norm; same reading as the published Lemma 4
--   - generalization: h^π closed convex → h convex with (2.2) at strictly positive points; closedness not assumed; reason: the statement concerns strictly positive iterates and (2.2) there; a closed convex regularizer is an instance
--   - reading: (2.2) for π′ ranging over all policies → (2.2) at strictly positive π′ only (the published IsKLStrongConvex); reason: at a boundary π′ with ω > 0 no finite h satisfies (2.2); every SPMD iterate is strictly positive; this is the convention of the published base mission
--   - reading: r chosen from {0, …, K−1} with P(r = i) = 2(i+2)/(K(K+3)) → r measurable, with that law, independent of the iterate sequence; reason: the source draws r after the run, so independently of it; same reading as the published Theorem 1
--   - encoding: K, the horizon → K ≥ 1; reason: the bound divides by Σ_{k<K}(k+2) and K(K+3), which vanish at K = 0
--   - encoding: ρ(π), a scalar → ρ^π(s₀) = avgCost at an arbitrary start state s₀; reason: under Assumption 1 the average cost does not depend on the start state (§2.1, p. 6), as in the published base items
--   - generalization: κ ≥ 0 in Assumption 3 → κ : ℝ appearing only through κ²; reason: replacing κ by |κ| leaves every hypothesis and conclusion unchanged; every source κ is included
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 12, Theorem 2 and (3.16); proof p. 12 (via Lemma 4, p. 10)

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting
import Definitions.Def_AvgRewardPMD_SPMD_Supplement_Actor

namespace AvgRewardPMD.SPMD.Supplement

open FoundationsML.ReinforcementLearning MeasureTheory ProbabilityTheory

theorem theorem_2 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P)
    (c : S → A → ℝ) (h : S → (A → ℝ) → ℝ) (ω L : ℝ) (hω : 0 < ω)
    (hconv : IsKLStrongConvex h ω) (hLip : IsL1Lipschitz h L)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) (νstar : S → ℝ)
    (hνstar : MarkovMixing.IsStationary (stateMatrix P πstar) νstar)
    {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (Qhat : ℕ → Ω → S × A → ℝ) (π : ℕ → Ω → S → A → ℝ)
    (bias κ : ℝ) (K : ℕ) (hK : 1 ≤ K)
    (hiter : IsSPMDIterates h (fun k => 2 / (ω * ((k : ℝ) + 1))) Qhat π)
    (hcrit : CriticAssumption μ ℱ (fun π' => diffQ P π' (fun s a => c s a + h s (π' s)))
      Qhat π bias κ K)
    (s₀ : S) :
    ((∑ k ∈ Finset.range K, ((k : ℝ) + 2))⁻¹ *
          ∑ k ∈ Finset.range K, ((k : ℝ) + 2) *
            ∫ ξ, (avgCost P (π k ξ) (fun s a => c s a + h s (π k ξ s)) s₀
              - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀) ∂μ
        + ω * ∫ ξ, stationaryKL νstar (π K ξ) πstar ∂μ
      ≤ 2 * ω / (K * (K + 3)) * stationaryKL νstar uniformPolicy πstar + bias
          + (2 * κ ^ 2 + 8 * L ^ 2) / (ω * (K + 3))) ∧
    (∀ r : Ω → ℕ, Measurable r →
      (∀ i < K, μ {ξ | r ξ = i} = ENNReal.ofReal (2 * ((i : ℝ) + 2) / (K * (K + 3)))) →
      IndepFun r (fun ξ k => π k ξ) μ →
      ∫ ξ, (avgCost P (π (r ξ) ξ) (fun s a => c s a + h s (π (r ξ) ξ s)) s₀
          - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀) ∂μ
        ≤ 2 * ω / (K * (K + 3)) * stationaryKL νstar uniformPolicy πstar + bias
          + (2 * κ ^ 2 + 8 * L ^ 2) / (ω * (K + 3))) := by sorry

end AvgRewardPMD.SPMD.Supplement
