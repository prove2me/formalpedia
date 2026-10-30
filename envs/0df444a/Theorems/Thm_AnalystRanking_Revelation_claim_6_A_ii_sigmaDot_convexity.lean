-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_claim_6_A_ii_sigmaDot_convexity
-- name    : AnalystRanking.Revelation.claim_6_A_ii_sigmaDot_convexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:55:05.638+00:00
-- url     : https://prove2.me/theorems/01ee01d3-fc9e-480f-ab8d-7eed4a8e7f7e
-- title:
--   Claim 6 (A)(ii): sign switch of $\partial\dot\sigma^l(q)/\partial\varphi$ at a unique $\ddot q$ (corrected: $\ddot q\in[\gamma,1)$)
-- statement:
--   Let $\gamma\in(\tfrac12,1)$, $\rho\in(0,1]$, $\varphi>1$, with $\rho>\bar\rho$ and $\varphi\ge\bar\varphi$ (high convexity and high correlation). Then there is a unique $\ddot q\in[\gamma,1)$, with $\ddot q>\gamma$ exactly when $\rho<1$, such that for every $q\in(0,1)$
--   $$\frac{\partial\dot\sigma^l(q)}{\partial\varphi}<0\ \text{ if } q<\ddot q,\qquad \frac{\partial\dot\sigma^l(q)}{\partial\varphi}\ge0\ \text{ if } q\ge\ddot q,$$
--   with $\dot\sigma^l$ of (B.34b).
--
--   On $[\tfrac12,\gamma]$ the interior strategy becomes less truthful as convexity grows, which drives Proposition 5 (B.1)'s convexity clause in regime A.2.
--
--   Differences from the source:
--   - correction: a unique q̈ ∈ (γ, 1) → a unique q̈ ∈ [γ, 1), with γ < q̈ ↔ ρ < 1; reason: the proof's N′(γ) = (2γ − 1)γ(1 − γ)(1 − ρ) vanishes at ρ = 1, where q̈ = γ; for ρ < 1 this is the printed claim
--   - encoding: ∂σ̇l(q)/∂φ → Mathlib deriv in φ of the second coordinate of sigmaDot; reason: deriv is 0 where the function is not differentiable, so a strict sign also asserts differentiability
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 6 (A)(ii), p. 50; proof, (B.43)–(B.44), pp. 51–52

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_sigmaDot
import Definitions.Def_AnalystRanking_Revelation_rhoBar
import Definitions.Def_AnalystRanking_Revelation_phiBar

namespace AnalystRanking.Revelation

/-- **Claim 6 (A)(ii): comparative statics of `σ̇ˡ(q)` in payoff convexity (corrected: `q̈ ∈ [γ, 1)`).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 6 (A)(ii), p. 50: "for high payoff convexity and high correlation, there exists a
unique `q̈ ∈ (γ, 1)` such that `∂σ̇ˡ(q)/∂φ < 0` if `q < q̈` and `∂σ̇ˡ(q)/∂φ ⩾ 0` if `q ⩾ q̈`",
with `σ̇ˡ` of (B.34b); "high payoff convexity and high correlation" is `ρ > ρ̄`, `φ ⩾ φ̄`
(Proposition 3 (A.2)).

**Formalization Note.** Correction: the proof's `N′(γ) = (2γ − 1)γ(1 − γ)(1 − ρ)` ((B.44), p. 52)
vanishes at `ρ = 1`, where `q̈ = γ`; so `q̈ ∈ [γ, 1)`, with `q̈ > γ` exactly when `ρ < 1`. For
`ρ < 1` this is the printed claim. `q` ranges over `(0, 1)`. -/
theorem claim_6_A_ii_sigmaDot_convexity (γ ρ φ : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1)
    (hρ1 : ρ ≤ 1) (hφ : 1 < φ) (hρbar : rhoBar γ < ρ) (hφbar : phiBar γ ρ ≤ φ) :
    ∃! qdd : ℝ, (γ ≤ qdd ∧ qdd < 1) ∧ (γ < qdd ↔ ρ < 1) ∧
      ∀ q : ℝ, 0 < q → q < 1 →
        (q < qdd → deriv (fun φ' => (sigmaDot γ ρ φ' q).2) φ < 0) ∧
        (qdd ≤ q → 0 ≤ deriv (fun φ' => (sigmaDot γ ρ φ' q).2) φ) := by sorry

end AnalystRanking.Revelation
