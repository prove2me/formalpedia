-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_three_point
-- name    : AvgRewardPMD.SPMD.three_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:08.226751+00:00
-- url     : https://prove2.me/theorems/a630f7a2-9764-445b-95ea-52b2285887a3
-- title:
--   (3.13), proof of Lemma 4, p. 10 — three-point inequality for the KL prox step (3.6) with a regularizer of modulus ω
-- statement:
--   Fix a state and drop it from the notation. Let $H:\Delta_{|\mathcal A|}\to\mathbb R$ be convex and satisfy (2.2) with modulus $\omega\ge0$: at every strictly positive $p'\in\Delta_{|\mathcal A|}$ some subgradient $g$ gives $H(p)-[H(p')+\langle g,p-p'\rangle]\ge\omega D^p_{p'}$ for all $p\in\Delta_{|\mathcal A|}$. Let $\lambda\ge0$, $Q\in\mathbb R^{|\mathcal A|}$, let $q\in\Delta_{|\mathcal A|}$ be strictly positive, and let $q^+\in\Delta_{|\mathcal A|}$ be a minimizer of the prox step
--   $$p\mapsto\lambda\big[\langle Q,p\rangle+H(p)\big]+D^p_q\quad\text{over }p\in\Delta_{|\mathcal A|}.$$
--   Then for every $p\in\Delta_{|\mathcal A|}$,
--   $$\lambda\big[\langle Q,q^+-p\rangle+H(q^+)-H(p)\big]+D^{q^+}_q\le D^p_q-(1+\lambda\omega)D^p_{q^+}.$$
--
--   With $Q=\bar{\mathcal Q}^{\pi_k,\zeta_k}(s,\cdot)$, $q=\pi_k(\cdot\mid s)$, $q^+=\pi_{k+1}(\cdot\mid s)$, $\lambda=\lambda_k$ and $H=h_s$ this is the paper's (3.13) for one step of SPMD. It is the first step of the proof of Lemma 4.
--
--   **Formalization Note** $D^p_q=\sum_a p(a)\log(p(a)/q(a))$ with `Real.log`; since $q$ is strictly positive, $D^p_q$ is the true KL divergence for every $p$. The theorem's hypotheses force $q^+$ to be strictly positive as well, so $D^p_{q^+}$ is the true KL divergence.
--
--   Differences from the source:
--   - encoding: Q̄^{π_k,ζ_k}(s,·), π_k(·|s), π_{k+1}(·|s) of the SPMD run at a state s → an arbitrary vector Q, a strictly positive q ∈ Δ_|A| and any minimizer q⁺ of the prox step; reason: (3.13) is a statement about one prox step at one state; every SPMD iterate is strictly positive (π_0 is uniform and each KL prox minimizer is strictly positive), so the SPMD step is an instance
--   - generalization: λ_k, a stepsize (positive) → any λ ≥ 0; reason: λ > 0 is an instance
--   - generalization: h^π closed convex → H convex on the simplex, closedness not assumed; reason: closed convex functions are an instance
--   - reading: (2.2) for π′ ranging over all policies, with "the subgradient" ∇h^{π′} → (2.2) at strictly positive π′ only, for some subgradient; reason: at a boundary π′ the KL D^π_{π′} is +∞ for some π, so with ω > 0 no finite h, not even the paper's example h^π = ωD^π_{π_0}, satisfies (2.2) there; on the strictly positive policies, (2.2) for some subgradient at every point makes H − ω·(negative entropy) convex there, hence holds for every subgradient, so the two readings agree
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 10, proof of Lemma 4, (3.13)

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting

namespace AvgRewardPMD.SPMD

theorem three_point {A : Type*} [Fintype A] [DecidableEq A] (H : (A → ℝ) → ℝ) (ω lam : ℝ)
    (hH : IsKLStrongConvexOn H ω) (hlam : 0 ≤ lam) (Q q qplus : A → ℝ)
    (hq : q ∈ stdSimplex ℝ A) (hqpos : ∀ a, 0 < q a) (hqplus : qplus ∈ stdSimplex ℝ A)
    (hmin : ∀ p ∈ stdSimplex ℝ A,
      lam * (∑ a, Q a * qplus a + H qplus) + kl qplus q ≤ lam * (∑ a, Q a * p a + H p) + kl p q) :
    ∀ p ∈ stdSimplex ℝ A,
      lam * (∑ a, Q a * (qplus a - p a) + H qplus - H p) + kl qplus q
        ≤ kl p q - (1 + lam * ω) * kl p qplus := by sorry

end AvgRewardPMD.SPMD
