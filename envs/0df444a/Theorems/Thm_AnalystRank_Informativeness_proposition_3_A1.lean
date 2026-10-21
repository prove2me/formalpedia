-- Prove2me | Theorems.Thm_AnalystRank_Informativeness_proposition_3_A1
-- name    : AnalystRank.Informativeness.proposition_3_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:59.245506+00:00
-- url     : https://prove2.me/theorems/b9b795b6-2db2-44b1-813f-5f2bbd3b920e
-- title:
--   Proposition 3 (A.1) — ρ > 0, φ > 1, ρ ≤ ρ̄ or φ ≤ φ̄: (1, 1) on [1 − q̌min, q̌min], (1, σ̌ˡ(q)) on (q̌min, q̌max), pooling beyond
-- statement:
--   Let $\gamma\in(\tfrac12,1)$, $\rho\in(0,1]$ and $w_1>w_0>w_2$ with a convex payoff, $\varphi>1$, and suppose either $\rho\le\bar\rho$, or $\rho>\bar\rho$ and $\varphi\le\bar\varphi$ (low correlation or low convexity). With $\check q_{\min}=\gamma-\chi\frac{\varphi-1}{(1-\gamma)\varphi+\gamma}$, $\check q_{\max}=\frac{\varphi\gamma}{1-\gamma+\varphi\gamma}$ and
--
--   $$\check\sigma^l(q)=1-\frac{\frac{(1-\gamma)\varphi+\gamma}{\varphi-1}(q-\gamma)+\chi}{q(1-\gamma)^2+(1-q)\gamma^2+\chi},\qquad \check\sigma^h(q)=\check\sigma^l(1-q),$$
--
--   for every prior $q\in(0,1)$ the rank game has a most informative equilibrium $\sigma$, and:
--
--   1. $\sigma=(1,1)$ if $q\in[1-\check q_{\min},\check q_{\min}]$;
--   2. $\check\sigma^h(q)\in(0,1)$ and $\sigma=(\check\sigma^h(q),1)$ if $q\in(1-\check q_{\max},1-\check q_{\min})$; $\check\sigma^l(q)\in(0,1)$ and $\sigma=(1,\check\sigma^l(q))$ if $q\in(\check q_{\min},\check q_{\max})$;
--   3. $\sigma^h=1-\sigma^l$ (pooling) if $q\in(0,1-\check q_{\max}]\cup[\check q_{\max},1)$.
--
--   With correlated signals and a convex payoff, the separating region shrinks from $[1-\gamma,\gamma]$ to $[1-\check q_{\min},\check q_{\min}]$. Just above $\check q_{\min}$, low-signal analysts sometimes forecast high. This is the existence half of the goal in this regime.
--
--   **Formalization Note** *Corrected (extended):* the printed condition is $1<\varphi<\bar\varphi$ when $\rho>\bar\rho$. At $\varphi=\bar\varphi$ the printed Part (A.2) fails, since its $\ddot\sigma^l$ would equal $1$ and $(1,1)$ is an equilibrium at $q=\tfrac12$. The description of (A.1) holds there, with $\check q_{\min}=\tfrac12$ (checked numerically), so (A.1) is stated for $\varphi\le\bar\varphi$ and (A.2) for $\varphi>\bar\varphi$.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), p. 15, Proposition 3 (A.1); (B.29)–(B.30), (B.42), pp. 45, 50 (boundary φ = φ̄ moved from (A.2) to (A.1))

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model
import Definitions.Def_AnalystRank_Informativeness_ClosedForms

namespace AnalystRank.Informativeness

open Set

theorem proposition_3_A1 (γ ρ w1 w0 w2 : ℝ) (hγ0 : 1 / 2 < γ) (hγ1 : γ < 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hw1 : w0 < w1) (hw2 : w2 < w0) (hφ : 1 < phi w1 w0 w2)
    (hreg : ρ ≤ rhoBar γ ∨ (rhoBar γ < ρ ∧ phi w1 w0 w2 ≤ phiBar γ ρ)) :
    ∀ q ∈ Ioo (0 : ℝ) 1,
      (∃ σ : ℝ × ℝ, IsMostInformative (rankEqSet w1 w0 w2 q γ ρ) σ) ∧
      ∀ σ : ℝ × ℝ, IsMostInformative (rankEqSet w1 w0 w2 q γ ρ) σ →
        (q ∈ Icc (1 - qmin γ ρ (phi w1 w0 w2)) (qmin γ ρ (phi w1 w0 w2)) → σ = (1, 1)) ∧
        (q ∈ Ioo (1 - qmaxCheck γ (phi w1 w0 w2)) (1 - qmin γ ρ (phi w1 w0 w2)) →
          sigmaCheckH γ ρ (phi w1 w0 w2) q ∈ Ioo (0 : ℝ) 1 ∧
          σ = (sigmaCheckH γ ρ (phi w1 w0 w2) q, 1)) ∧
        (q ∈ Ioo (qmin γ ρ (phi w1 w0 w2)) (qmaxCheck γ (phi w1 w0 w2)) →
          sigmaCheckL γ ρ (phi w1 w0 w2) q ∈ Ioo (0 : ℝ) 1 ∧
          σ = (1, sigmaCheckL γ ρ (phi w1 w0 w2) q)) ∧
        ((q ≤ 1 - qmaxCheck γ (phi w1 w0 w2) ∨ qmaxCheck γ (phi w1 w0 w2) ≤ q) →
          σ.1 = 1 - σ.2) := by sorry

end AnalystRank.Informativeness
