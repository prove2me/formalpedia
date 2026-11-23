-- Prove2me | Theorems.Thm_FiniteTD_Markov_Supplement_lemma_21
-- name    : FiniteTD.Markov.Supplement.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:42:17.221852+00:00
-- url     : https://prove2.me/theorems/e324e8e2-0586-43cf-864a-0c854d0ca0fe
-- title:
--   Lemma 21, p. 48 — descent inequality for the expected update of a D-projected contraction Π_D H
-- statement:
--   Let $S$ be a finite state space with stochastic matrix $P$ and stationary distribution $\pi$, $D=\mathrm{diag}(\pi)$, features $\phi(s)\in\mathbb R^d$ with feature matrix $\Phi$, and assume $\Sigma=\Phi^\top D\Phi$ has full rank ($\omega>0$ its minimum eigenvalue). Let $\Pi_D$ be the $\langle\cdot,\cdot\rangle_D$-orthogonal projection onto the span of the features and let $H$ be any operator on value functions $V:S\to\mathbb R$ such that $\Pi_DH$ is a contraction for $\|\cdot\|_D$ with modulus $c\in[0,1)$:
--   $$\|\Pi_DHV-\Pi_DHV'\|_D\le c\,\|V-V'\|_D\qquad\text{for all }V,V'.$$
--   Let $V_{\theta^*}=\Phi\theta^*$ be the fixed point, $V_{\theta^*}=\Pi_DHV_{\theta^*}$, and define the expected update $\bar g(\theta)=\Phi^\top D(H\Phi\theta-\Phi\theta)$. Then for every $\theta\in\mathbb R^d$,
--   $$(\theta^*-\theta)^\top\bar g(\theta)\ge(1-c)\,\|V_{\theta^*}-V_\theta\|_D^2.$$
--
--   The lemma isolates the only property of the Bellman operator used in the descent inequalities of the paper; applied to $T^{(\lambda)}$ it gives Lemma 16, and applied to the optimal-stopping operator it gives Lemma 13.
--
--   **Formalization Note** $H$ is arbitrary (not assumed linear or monotone). $\Pi_D=\Phi\Sigma^{-1}\Phi^\top D$; the paper's proof uses that $\Pi_D$ is self-adjoint for $\langle\cdot,\cdot\rangle_D$.
--
--   Differences from the source:
--
--   - encoding: ω > 0 is the minimum eigenvalue of Σ = Σ_s π(s)φ(s)φ(s)⊤ → ω is the least value of θ⊤Σθ on the Euclidean unit sphere, and 0 < ω; reason: Rayleigh-quotient characterisation of λ_min(Σ); full rank of Σ is 0 < ω
--   - encoding: the contraction modulus is called γ → the modulus is called c, with 0 ≤ c < 1; reason: γ denotes the discount factor elsewhere; a contraction modulus lies in [0, 1)
--   - encoding: V_θ* is the unique fixed point of Π_D H → Φθ* is a fixed point of Π_D H; reason: Two fixed points lie in the feature span; contraction makes their D-distance zero, and full-rank Σ makes their coefficients equal. Thus uniqueness of fixed points in the feature span follows even if π has zero entries.
--   - encoding: Π_D is the D-weighted orthogonal projection onto span Φ → Π_D = Φ(Φ⊤DΦ)⁻¹Φ⊤D; reason: this is the projection when Σ has full rank, which the paper assumes on p. 6
--   - generalization: the chain is ergodic with a unique limiting stationary distribution (p. 5); Appendix B additionally assumes Assumption 1 → P is stochastic and π is a stationary distribution; no ergodicity or uniform mixing hypothesis; reason: All source chains satisfy these hypotheses. These particular bounds use the stationary one-step law or deterministic operator/trace bounds, so they also cover periodic and reducible chains; the finite-time bias and Markov convergence bounds in Lemma 20 and Theorem 4 retain Assumption 1.
--   - generalization: features obey ‖φ(s)‖₂ ≤ 1 (p. 6) → no feature-normalization hypothesis; reason: The source normalized features are included. Descent depends on the projected contraction and the full-rank covariance, and does not use the feature norm bound.
--   - encoding: π is the stationary weight defining D → an auxiliary stochastic P with stationary distribution π; reason: P is absent from H, the contraction and the conclusion. Every source π admits such a P (in particular the identity kernel), so this binder excludes no source instance.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 48, Lemma 21 (Appendix C)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_Lambda

namespace FiniteTD.Markov.Supplement

open scoped InnerProductSpace

theorem lemma_21 {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (ω : ℝ)
    (H : (S → ℝ) → (S → ℝ)) (c : ℝ) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π)
    (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcontr : ∀ v v' : S → ℝ,
      dNormV π (projD π φ (H v) - projD π φ (H v')) ≤ c * dNormV π (v - v'))
    (hfix : valFn φ θstar = projD π φ (H (valFn φ θstar))) :
    ∀ θ : EuclideanSpace ℝ (Fin d),
      (1 - c) * dNormSq π φ (θstar - θ) ≤ ⟪θstar - θ, gbarH π φ H θ⟫_ℝ := by sorry

end FiniteTD.Markov.Supplement
