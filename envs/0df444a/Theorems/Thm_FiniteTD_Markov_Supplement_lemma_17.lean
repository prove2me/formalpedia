-- Prove2me | Theorems.Thm_FiniteTD_Markov_Supplement_lemma_17
-- name    : FiniteTD.Markov.Supplement.lemma_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:43:30.151137+00:00
-- url     : https://prove2.me/theorems/72e9965f-5c08-4833-bdb5-94cdcd9e16cf
-- title:
--   Lemma 17, p. 40 — the TD(λ) update and its steady-state mean are bounded by B on Θ_R
-- statement:
--   Let $S$ be a finite state space with stochastic matrix $P$ and stationary distribution $\pi$, rewards with $|R(s,s')|\le r_{\max}$, $\gamma\in[0,1)$, $\lambda\in[0,1]$, features with $\|\phi(s)\|_2\le1$, and set $B=(r_{\max}+2R)/(1-\gamma\lambda)$. For $\theta$ in $\Theta_R=\{\theta:\|\theta\|_2\le R\}$:
--
--   1. along every state path $s_0,s_1,\dots$ and at every time $t$, the TD(λ) update $x_t(\theta,z_{0:t})=\delta_t(\theta)z_{0:t}$, with $\delta_t(\theta)=R(s_t,s_{t+1})+\gamma\phi(s_{t+1})^\top\theta-\phi(s_t)^\top\theta$ and $z_{0:t}=\sum_{k=0}^t(\gamma\lambda)^k\phi(s_{t-k})$, satisfies $\|x_t(\theta,z_{0:t})\|_2\le B$;
--   2. the steady-state mean update satisfies $\|\bar x(\theta)\|_2\le B$.
--
--   $B$ plays for TD(λ) the role of the gradient bound $G=r_{\max}+2R$ of TD(0) (Lemma 6), enlarged by the factor $1/(1-\gamma\lambda)$ that the trace contributes.
--
--   **Formalization Note** $\bar x(\theta)=\Phi^\top D(T^{(\lambda)}\Phi\theta-\Phi\theta)$ (39).
--
--   Differences from the source:
--
--   - reading: the discount factor satisfies γ < 1 → 0 ≤ γ < 1; reason: a discount factor is nonnegative; §10 writes γ ∈ [0, 1), and the Cauchy–Schwarz step of Lemma 3 uses γ ≥ 0; the published goal uses the same convention
--   - reading: x̄(θ) = lim_t E[δ_t(θ) z_{0:t}], equivalently (38)–(39) → x̄(θ) = Φ⊤D(T^{(λ)}Φθ − Φθ), the right side of (39); reason: the paper states (38) and (39) as equal on p. 38 and uses (39) in Lemma 16; on a finite chain the backward-view series (38) is exactly (39)
--   - generalization: the bound holds with probability 1 → the bound holds for every state path; reason: the inequality is pathwise and uses only the bounds on rewards and features; every path, of positive probability or not, is covered, which specialises to the almost-sure statement
--   - generalization: the chain is ergodic with a unique limiting stationary distribution (p. 5); Appendix B additionally assumes Assumption 1 → P is stochastic and π is a stationary distribution; no ergodicity or uniform mixing hypothesis; reason: All source chains satisfy these hypotheses. These particular bounds use the stationary one-step law or deterministic operator/trace bounds, so they also cover periodic and reducible chains; the finite-time bias and Markov convergence bounds in Lemma 20 and Theorem 4 retain Assumption 1.
--   - generalization: full-rank Σ, positive minimum eigenvalue, and R ≥ ‖θ*‖₂ in the Appendix B setting → no rank or target hypothesis; any R and θ with ‖θ‖ ≤ R; reason: Update bounds depend on reward, feature and trace bounds only. No projection inverse is used by xbar; the source settings are all included. A nonempty ball implies R ≥ 0, and stationarity implies S is nonempty and rmax ≥ 0.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 40, Lemma 17 (proof p. 45–46)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_Lambda

namespace FiniteTD.Markov.Supplement

theorem lemma_17 {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ lam : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ)
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) :
    ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ R →
      (∀ (w : ℕ → S) (t : ℕ),
        ‖tdErr γ Rw φ θ (w t) (w (t + 1)) • traceN φ (γ * lam) w t‖ ≤
          (rmax + 2 * R) / (1 - γ * lam)) ∧
      ‖xbar π P γ lam Rw φ θ‖ ≤ (rmax + 2 * R) / (1 - γ * lam) := by sorry

end FiniteTD.Markov.Supplement
