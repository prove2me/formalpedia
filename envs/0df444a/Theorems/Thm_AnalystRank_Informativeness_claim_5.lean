-- Prove2me | Theorems.Thm_AnalystRank_Informativeness_claim_5
-- name    : AnalystRank.Informativeness.claim_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:22.901348+00:00
-- url     : https://prove2.me/theorems/e924c148-6acd-44c5-bfa4-625f76f9c45c
-- title:
--   Claim 5 — beyond q_min there is no equilibrium (σʰ ∈ (0,1), 1) if φ > 1, and none (1, σˡ ∈ (0,1)) if φ < 1
-- statement:
--   Let $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$, $w_1>w_0>w_2$, and $q<1$. Write $q_{\min}=\gamma-\chi\frac{\varphi-1}{(1-\gamma)\varphi+\gamma}$, so that $q_{\min}=\gamma$ when $\rho=0$, $q_{\min}=\check q_{\min}$ when $\varphi>1$ and $q_{\min}=\hat q_{\min}$ when $\varphi<1$.
--
--   1. **(A)** If $\varphi>1$ and $q>q_{\min}$, the rank game has no equilibrium of the form $(\sigma^h,1)$ with $\sigma^h\in(0,1)$.
--   2. **(B)** If $\varphi<1$ and $q>q_{\min}$, the rank game has no equilibrium of the form $(1,\sigma^l)$ with $\sigma^l\in(0,1)$.
--
--   At low prior uncertainty only one of the two semi-separating shapes can occur, depending on the curvature of the payoff.
--
--   **Formalization Note** The paper's two cases "$q>\gamma$ if $\rho=0$" and "$q>\check q_{\min}$ (resp. $\hat q_{\min}$) if $\rho>0$" are merged through $q_{\min}=\gamma$ at $\rho=0$.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), p. 35, Claim 5

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model

namespace AnalystRank.Informativeness

open Set

theorem claim_5 (q γ ρ w1 w0 w2 : ℝ) (hq1 : q < 1) (hγ0 : 1 / 2 < γ) (hγ1 : γ < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hw1 : w0 < w1) (hw2 : w2 < w0) :
    (1 < phi w1 w0 w2 → qmin γ ρ (phi w1 w0 w2) < q →
      ∀ h ∈ Ioo (0 : ℝ) 1, (h, (1 : ℝ)) ∉ rankEqSet w1 w0 w2 q γ ρ) ∧
    (phi w1 w0 w2 < 1 → qmin γ ρ (phi w1 w0 w2) < q →
      ∀ l ∈ Ioo (0 : ℝ) 1, ((1 : ℝ), l) ∉ rankEqSet w1 w0 w2 q γ ρ) := by sorry

end AnalystRank.Informativeness
