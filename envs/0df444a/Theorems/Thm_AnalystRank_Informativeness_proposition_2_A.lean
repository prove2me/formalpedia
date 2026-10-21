-- Prove2me | Theorems.Thm_AnalystRank_Informativeness_proposition_2_A
-- name    : AnalystRank.Informativeness.proposition_2_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:03.563605+00:00
-- url     : https://prove2.me/theorems/55510c25-bfa9-4fb8-87f6-456f8062eb14
-- title:
--   Proposition 2 (A) — ρ = 0, φ > 1: the most informative equilibrium exists; (1, 1) on [1 − γ, γ], (1, σ̌ˡ₀(q)) on (γ, q̌max), pooling beyond
-- statement:
--   Let $\gamma\in(\tfrac12,1)$, uncorrelated signals ($\rho=0$), and $w_1>w_0>w_2$ with a convex payoff, $\varphi>1$. Let $\check q_{\max}=\frac{\varphi\gamma}{1-\gamma+\varphi\gamma}$ and
--
--   $$\check\sigma^l_0(q)=1-\frac{\frac{(1-\gamma)\varphi+\gamma}{\varphi-1}(q-\gamma)}{q(1-\gamma)^2+(1-q)\gamma^2},\qquad \check\sigma^h_0(q)=\check\sigma^l_0(1-q).$$
--
--   For every prior $q\in(0,1)$ the rank game has a most informative equilibrium $\sigma$, and:
--
--   1. $\sigma=(1,1)$ if $q\in[1-\gamma,\gamma]$;
--   2. $\check\sigma^h_0(q)\in(0,1)$ and $\sigma=(\check\sigma^h_0(q),1)$ if $q\in(1-\check q_{\max},1-\gamma)$; $\check\sigma^l_0(q)\in(0,1)$ and $\sigma=(1,\check\sigma^l_0(q))$ if $q\in(\gamma,\check q_{\max})$;
--   3. $\sigma^h=1-\sigma^l$ (pooling) if $q\in(0,1-\check q_{\max}]\cup[\check q_{\max},1)$.
--
--   Without correlation, competition leaves the separating region of the benchmark unchanged and replaces part of its pooling region by semi-separating equilibria.
--
--   **Formalization Note** $\check\sigma^l_0$ is taken from (B.21). The summary (B.28) prints the factor $(1-\varphi)$ in place of $(\varphi-1)$, a sign slip that would make $\check\sigma^l_0>1$ on $(\gamma,\check q_{\max})$.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), pp. 12–13, Proposition 2 (A); (B.21)–(B.22), p. 42

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model
import Definitions.Def_AnalystRank_Informativeness_ClosedForms

namespace AnalystRank.Informativeness

open Set

theorem proposition_2_A (γ w1 w0 w2 : ℝ) (hγ0 : 1 / 2 < γ) (hγ1 : γ < 1)
    (hw1 : w0 < w1) (hw2 : w2 < w0) (hφ : 1 < phi w1 w0 w2) :
    ∀ q ∈ Ioo (0 : ℝ) 1,
      (∃ σ : ℝ × ℝ, IsMostInformative (rankEqSet w1 w0 w2 q γ 0) σ) ∧
      ∀ σ : ℝ × ℝ, IsMostInformative (rankEqSet w1 w0 w2 q γ 0) σ →
        (q ∈ Icc (1 - γ) γ → σ = (1, 1)) ∧
        (q ∈ Ioo (1 - qmaxCheck γ (phi w1 w0 w2)) (1 - γ) →
          sigmaCheckH0 γ (phi w1 w0 w2) q ∈ Ioo (0 : ℝ) 1 ∧
          σ = (sigmaCheckH0 γ (phi w1 w0 w2) q, 1)) ∧
        (q ∈ Ioo γ (qmaxCheck γ (phi w1 w0 w2)) →
          sigmaCheckL0 γ (phi w1 w0 w2) q ∈ Ioo (0 : ℝ) 1 ∧
          σ = (1, sigmaCheckL0 γ (phi w1 w0 w2) q)) ∧
        ((q ≤ 1 - qmaxCheck γ (phi w1 w0 w2) ∨ qmaxCheck γ (phi w1 w0 w2) ≤ q) →
          σ.1 = 1 - σ.2) := by sorry

end AnalystRank.Informativeness
