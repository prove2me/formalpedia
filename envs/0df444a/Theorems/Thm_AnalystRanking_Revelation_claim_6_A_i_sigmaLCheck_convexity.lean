-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_claim_6_A_i_sigmaLCheck_convexity
-- name    : AnalystRanking.Revelation.claim_6_A_i_sigmaLCheck_convexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:54:34.570636+00:00
-- url     : https://prove2.me/theorems/88f71bc4-d2d5-4da7-89bd-0c0e747d0662
-- title:
--   Claim 6 (A)(i): $\partial\check\sigma^l(q)/\partial\varphi<0$ for $q<\gamma$, $\ge0$ for $q\ge\gamma$
-- statement:
--   Standing assumptions (§2): $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$, $q\in(0,1)$. For $\varphi>1$ and $\check\sigma^l$ of (B.30),
--   $$\frac{\partial\check\sigma^l(q)}{\partial\varphi}<0\ \text{ if } q<\gamma,\qquad \frac{\partial\check\sigma^l(q)}{\partial\varphi}\ge0\ \text{ if } q\ge\gamma .$$
--
--   Below $\gamma$, more convex payoffs make the low-signal analyst understate his signal more often; this is the source of the strict part of Proposition 5 (B.1)'s convexity clause.
--
--   Differences from the source:
--   - encoding: ∂σ̌l(q)/∂φ → Mathlib deriv in φ; reason: deriv is 0 where the function is not differentiable, so a strict sign also asserts differentiability
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 6 (A)(i), p. 50

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_sigmaLCheck

namespace AnalystRanking.Revelation

/-- **Claim 6 (A)(i): comparative statics of `σ̌ˡ(q)` in payoff convexity.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 6 (A)(i), p. 50: "for a convex payoff structure, `∂σ̌ˡ(q)/∂φ < 0` if `q < γ` and
`∂σ̌ˡ(q)/∂φ ⩾ 0` if `q ⩾ γ`", with `σ̌ˡ` of (B.30).

**Formalization Note.** `deriv` is Mathlib's derivative in `φ` (at `φ > 1` the function is
differentiable). Standing assumptions of §2. -/
theorem claim_6_A_i_sigmaLCheck_convexity (γ ρ q φ : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hφ : 1 < φ) :
    (q < γ → deriv (fun φ' => sigmaLCheck γ ρ φ' q) φ < 0) ∧
      (γ ≤ q → 0 ≤ deriv (fun φ' => sigmaLCheck γ ρ φ' q) φ) := by sorry

end AnalystRanking.Revelation
