-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_Supplement_lemma_5
-- name    : AvgRewardPMD.SPMD.Supplement.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:25:40.828094+00:00
-- url     : https://prove2.me/theorems/ddf87385-66e3-4ab4-bd7f-05f783b05d38
-- title:
--   Lemma 5, p. 13 — pointwise: (ρ(π_{k+1})−ρ(π_k))/(1−Γ) ≤ ⟨Q̂_k(s,·),π_{k+1}−π_k⟩ + h^{π_{k+1}}(s)−h^{π_k}(s) + D^{π_{k+1}}_{π_k}(s)/λ_k + λ_k‖δ_k‖²_sp/(8(1−Γ))
-- statement:
--   Let $\mathcal M=(\mathcal S,\mathcal A,\mathsf P,c)$ be a finite AMDP satisfying the mixing Assumption 1 and the ergodicity Assumption 2, and let $\Gamma\in(0,1)$ satisfy $\min_s\nu^\pi(s)\ge1-\Gamma$ for every feasible policy $\pi$. Let the regularizer $h^\pi(s)=h_s(\pi(\cdot\mid s))$ be convex with modulus $\omega>0$ in the sense of (2.2), and let $\rho(\pi)$ and $\bar Q^\pi$ be the average cost and the basic differential Q-function of the regularized cost $c(s,a)+h^\pi(s)$.
--
--   Let $\pi_0,\pi_1,\dots$ be SPMD iterates (Algorithm 1, (3.6)) driven by critic outputs $\bar{\mathcal Q}^{\pi_k,\zeta_k}$, on one sample path, with stepsizes $\lambda_j>0$ for $j\le k$, and let $\delta_k=\bar{\mathcal Q}^{\pi_k,\zeta_k}-\bar Q^{\pi_k}$. Then for every $s\in\mathcal S$,
--   $$\frac{1}{1-\Gamma}\big(\rho(\pi_{k+1})-\rho(\pi_k)\big)\le\big\langle\bar{\mathcal Q}^{\pi_k,\zeta_k}(s,\cdot),\pi_{k+1}(\cdot\mid s)-\pi_k(\cdot\mid s)\big\rangle+h^{\pi_{k+1}}(s)-h^{\pi_k}(s)+\frac1{\lambda_k}D^{\pi_{k+1}}_{\pi_k}(s)+\frac{\lambda_k\|\delta_k\|_{\mathrm{sp}}^2}{8(1-\Gamma)} .$$
--
--   The inequality transfers the improvement of the average cost, a global quantity weighted by the unknown stationary law of $\pi_{k+1}$, to the per-state prox step at an arbitrary state $s$; it is the first step towards the linear recursion of Lemma 6.
--
--   **Formalization Note** The statement holds on every sample point; no measure is involved. $D^{p}_{q}(s)$ is the KL divergence $\sum_a p(a\mid s)\log\frac{p(a\mid s)}{q(a\mid s)}$ (`kl`), with the first argument the new iterate.
--
--   Differences from the source:
--   - generalization: stepsizes λ_k > 0 at every step → λ_j > 0 for j ≤ k only; reason: steps after k do not enter the inequality at step k; positive stepsizes at every step are an instance
--   - generalization: h^π closed convex → h convex with (2.2) at strictly positive points; closedness not assumed; reason: the statement concerns strictly positive iterates and (2.2) there; a closed convex regularizer is an instance
--   - reading: (2.2) for π′ ranging over all policies → (2.2) at strictly positive π′ only (the published IsKLStrongConvex); reason: at a boundary π′ with ω > 0 no finite h satisfies (2.2); every SPMD iterate is strictly positive; this is the convention of the published base mission
--   - encoding: ρ(π), a scalar → ρ^π(s₀) = avgCost at an arbitrary start state s₀; reason: under Assumption 1 the average cost does not depend on the start state (§2.1, p. 6), as in the published base items
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 13, Lemma 5; proof p. 13 (via Lemma 2, p. 7, and (3.13), p. 10)

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting
import Definitions.Def_AvgRewardPMD_SPMD_Supplement_Actor

namespace AvgRewardPMD.SPMD.Supplement

open FoundationsML.ReinforcementLearning

theorem lemma_5 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P) (herg : IsErgodic P)
    (c : S → A → ℝ) (h : S → (A → ℝ) → ℝ) (ω : ℝ) (hω : 0 < ω)
    (hconv : IsKLStrongConvex h ω) (Γ : ℝ) (hΓ : IsGammaBound P Γ)
    {Ω : Type*} (Qhat : ℕ → Ω → S × A → ℝ) (π : ℕ → Ω → S → A → ℝ) (lam : ℕ → ℝ)
    (hiter : IsSPMDIterates h lam Qhat π) (k : ℕ) (hlam : ∀ j ≤ k, 0 < lam j) (ξ : Ω) (s s₀ : S) :
    (avgCost P (π (k + 1) ξ) (fun s a => c s a + h s (π (k + 1) ξ s)) s₀
        - avgCost P (π k ξ) (fun s a => c s a + h s (π k ξ s)) s₀) / (1 - Γ)
      ≤ ∑ a, Qhat k ξ (s, a) * (π (k + 1) ξ s a - π k ξ s a)
          + h s (π (k + 1) ξ s) - h s (π k ξ s)
          + kl (π (k + 1) ξ s) (π k ξ s) / lam k
          + lam k * span (fun x => Qhat k ξ x
              - diffQ P (π k ξ) (fun s a => c s a + h s (π k ξ s)) x) ^ 2 / (8 * (1 - Γ)) := by sorry

end AvgRewardPMD.SPMD.Supplement
