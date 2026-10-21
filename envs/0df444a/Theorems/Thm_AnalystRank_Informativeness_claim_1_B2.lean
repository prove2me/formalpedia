-- Prove2me | Theorems.Thm_AnalystRank_Informativeness_claim_1_B2
-- name    : AnalystRank.Informativeness.claim_1_B2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:03.106944+00:00
-- url     : https://prove2.me/theorems/8999a8f6-6487-4f60-861c-ccd84b964d0e
-- title:
--   Claim 1 (B.2) — q̌min > 1/2 if ρ ≤ ρ̄ or 1 < φ < φ̄, and q̌min ≤ 1/2 if ρ > ρ̄ and φ ≥ φ̄, with ρ̄ > 0 and φ̄ > 1
-- statement:
--   Let $\gamma\in(\tfrac12,1)$, $\rho\in(0,1]$ and $w_1>w_0>w_2$ with convex payoffs, $\varphi=(w_1-w_0)/(w_0-w_2)>1$. With $\chi=\rho\gamma(1-\gamma)$, put
--
--   $$\bar\rho=1-\frac1{2\gamma},\qquad \bar\varphi=\frac{\chi+\gamma(\gamma-\frac12)}{\chi-(1-\gamma)(\gamma-\frac12)},\qquad \check q_{\min}=\gamma-\chi\,\frac{\varphi-1}{(1-\gamma)\varphi+\gamma}.$$
--
--   Then:
--
--   1. $\bar\rho>0$, and $\bar\varphi>1$ whenever $\rho>\bar\rho$;
--   2. if $\rho\le\bar\rho$, or $\rho>\bar\rho$ and $\varphi<\bar\varphi$, then $\check q_{\min}>\tfrac12$;
--   3. if $\rho>\bar\rho$ and $\varphi\ge\bar\varphi$, then $\check q_{\min}\le\tfrac12$.
--
--   The claim splits the convex case into two regimes. In the first, the separating equilibrium survives on a nonempty interval around $q=\tfrac12$. In the second (high correlation, high convexity), it exists at no prior above one half, except at $q=\tfrac12$ when $\varphi=\bar\varphi$.
--
--   **Formalization Note** The paper's "there exist $\bar\rho>0$ and $\bar\varphi>1$" refers to the explicit formulas (B.3)–(B.4), which are stated here instead of a bare existential.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), p. 34, Claim 1 (B.2), (B.3)–(B.4)

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model
import Definitions.Def_AnalystRank_Informativeness_ClosedForms

namespace AnalystRank.Informativeness

open Set

theorem claim_1_B2 (γ ρ w1 w0 w2 : ℝ) (hγ0 : 1 / 2 < γ) (hγ1 : γ < 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hw1 : w0 < w1) (hw2 : w2 < w0) (hφ : 1 < phi w1 w0 w2) :
    0 < rhoBar γ ∧
    (rhoBar γ < ρ → 1 < phiBar γ ρ) ∧
    ((ρ ≤ rhoBar γ ∨ (rhoBar γ < ρ ∧ phi w1 w0 w2 < phiBar γ ρ)) →
      1 / 2 < qmin γ ρ (phi w1 w0 w2)) ∧
    (rhoBar γ < ρ → phiBar γ ρ ≤ phi w1 w0 w2 → qmin γ ρ (phi w1 w0 w2) ≤ 1 / 2) := by sorry

end AnalystRank.Informativeness
