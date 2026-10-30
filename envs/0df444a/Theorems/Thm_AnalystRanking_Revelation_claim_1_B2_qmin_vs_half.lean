-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_claim_1_B2_qmin_vs_half
-- name    : AnalystRanking.Revelation.claim_1_B2_qmin_vs_half
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:46:28.427739+00:00
-- url     : https://prove2.me/theorems/c6c33df8-7eb2-47c3-a79d-19e8be9360c2
-- title:
--   Claim 1 (B.2): $\check q_{\min}>\tfrac12$ unless correlation and convexity are both high
-- statement:
--   Let $\gamma\in(\tfrac12,1)$, $\rho\in(0,1]$ and $\varphi>1$, and let
--   $$\bar\rho=1-\frac1{2\gamma},\qquad \bar\varphi=\frac{\chi+\gamma(\gamma-\tfrac12)}{\chi-(1-\gamma)(\gamma-\tfrac12)},\qquad \chi=\rho\gamma(1-\gamma).$$
--   Then $\bar\rho>0$; if $\rho>\bar\rho$ then $\bar\varphi>1$; and
--
--   1. if $\rho\le\bar\rho$, or $\rho>\bar\rho$ and $1<\varphi<\bar\varphi$, then $\check q_{\min}>\tfrac12$;
--   2. if $\rho>\bar\rho$ and $\varphi\ge\bar\varphi$, then $\check q_{\min}\le\tfrac12$.
--
--   Here $\check q_{\min}$ is $q_{\min}$ of (B.2). The thresholds split Proposition 3 (A) into the regimes A.1 (a separating equilibrium exists at some prior) and A.2 (it exists at no prior).
--
--   Differences from the source:
--   - reading: There exist ρ̄ > 0 and φ̄ > 1 (with ρ̄, φ̄ given by (B.3)–(B.4)) → 0 < rhoBar γ, and rhoBar γ < ρ → 1 < phiBar γ ρ; reason: φ̄ is used only when ρ > ρ̄; for ρ ≤ ρ̄ the denominator of (B.4) is not positive and φ̄ plays no role
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 1 (B.2), displays (B.3)–(B.4), p. 34

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_qminCheck
import Definitions.Def_AnalystRanking_Revelation_rhoBar
import Definitions.Def_AnalystRanking_Revelation_phiBar

namespace AnalystRanking.Revelation

/-- **Claim 1 (B.2): when `q̌_min` exceeds `1/2`.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 1 (B.2), p. 34: "There exist `ρ̄ > 0` and `φ̄ > 1` such that if either `ρ ⩽ ρ̄`, or
`ρ > ρ̄` and `1 < φ < φ̄`, then `q̌_min > 1/2`; however, if `ρ > ρ̄` and `φ ⩾ φ̄`, then
`q̌_min ⩽ 1/2`, where `ρ̄ ≡ 1 − 1/(2γ)` (B.3), `φ̄ ≡ (χ + γ(γ − 1/2))/(χ − (1 − γ)(γ − 1/2))` (B.4)."

**Formalization Note.** `q̌_min = q_min(φ > 1)` ((B.1), p. 33), so `φ > 1` is assumed. `φ̄` is used
by the paper only when `ρ > ρ̄` (its denominator is positive exactly then), so `φ̄ > 1` is stated
under `ρ > ρ̄`. Claim 1 (B) assumes `ρ > 0`. -/
theorem claim_1_B2_qmin_vs_half (γ ρ φ : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hφ : 1 < φ) :
    0 < rhoBar γ ∧ (rhoBar γ < ρ → 1 < phiBar γ ρ) ∧
      ((ρ ≤ rhoBar γ ∨ (rhoBar γ < ρ ∧ φ < phiBar γ ρ)) → 1 / 2 < qminCheck γ ρ φ) ∧
      (rhoBar γ < ρ → phiBar γ ρ ≤ φ → qminCheck γ ρ φ ≤ 1 / 2) := by sorry

end AnalystRanking.Revelation
