-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_claim_3_B2_unique_crossing
-- name    : AnalystRanking.Revelation.claim_3_B2_unique_crossing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:48:51.851071+00:00
-- url     : https://prove2.me/theorems/a3666743-c734-4754-9135-53f1c852bcd6
-- title:
--   Claim 3 (B.2): unique crossing $\ddot\sigma^l$ of $g_l(1,\cdot)$ and $g_h(1,\cdot)$ (corrected: $\ddot\sigma^l\in(0,1]$, $<1$ iff $\varphi>\bar\varphi$)
-- statement:
--   Let $\gamma\in(\tfrac12,1)$, $\rho\in(0,1]$, $\varphi>1$, and suppose $\rho>\bar\rho$ and $\varphi\ge\bar\varphi$. Then there is a unique $\ddot\sigma^l\in(0,1]$ such that
--   $$g_l(1,\ddot\sigma^l)=g_h(1,\ddot\sigma^l)\quad\text{(B.6)},$$
--   $g_l(1,\sigma^l)\ge g_h(1,\sigma^l)$ for $\sigma^l\in[0,\ddot\sigma^l]$, and $g_l(1,\sigma^l)<g_h(1,\sigma^l)$ for $\sigma^l\in(\ddot\sigma^l,1]$. Moreover $\ddot\sigma^l<1$ exactly when $\varphi>\bar\varphi$.
--
--   The crossing determines the prior $\bar q=g_l(1,\ddot\sigma^l)/(1+g_l(1,\ddot\sigma^l))$ that separates the two kinds of equilibria in Proposition 3 (A.2).
--
--   Differences from the source:
--   - correction: a unique σ̈l ∈ (0, 1) with the crossing property, whenever ρ > ρ̄ and φ ⩾ φ̄ → a unique σ̈l ∈ (0, 1], with σ̈l < 1 ↔ φ̄ < φ; reason: at φ = φ̄, g_l(1,1) = g_h(1,1) (both are the odds at q̌min = 1/2) and g_l(1,σl) > g_h(1,σl) for σl < 1, so no σ̈l ∈ (0,1) has the property; e.g. γ = 0.75, ρ = 0.8, φ = φ̄ = 27/7. For φ > φ̄ the statement is the printed one
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 3 (B.2), pp. 34–35, display (B.6), p. 35

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_gl
import Definitions.Def_AnalystRanking_Revelation_gh
import Definitions.Def_AnalystRanking_Revelation_rhoBar
import Definitions.Def_AnalystRanking_Revelation_phiBar

namespace AnalystRanking.Revelation

/-- **Claim 3 (B.2): the unique crossing `σ̈ˡ` of `g_l(1, ·)` and `g_h(1, ·)` (corrected at `φ = φ̄`).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 3 (B.2), pp. 34–35: "If `ρ > ρ̄` and `φ ⩾ φ̄`, then there exists a unique `σ̈ˡ ∈ (0, 1)`
such that `g_l(1, σˡ) ⩾ g_h(1, σˡ)` if `σˡ ⩽ σ̈ˡ`, and `g_l(1, σˡ) < g_h(1, σˡ)` if `σˡ > σ̈ˡ`, …
and `σ̈ˡ` is implicitly defined as `g_l(1, σ̈ˡ) = g_h(1, σ̈ˡ)` (B.6)."

**Formalization Note.** Correction: at `φ = φ̄`, `g_l(1, 1) = g_h(1, 1)` (both equal to the odds of
`q̌_min = 1/2`) and `g_l(1, σˡ) > g_h(1, σˡ)` for `σˡ < 1`, so no `σ̈ˡ ∈ (0, 1)` has the stated
property; e.g. `γ = 0.75`, `ρ = 0.8`, `φ = φ̄ = 27/7`. The crossing is stated in `(0, 1]`, with
`σ̈ˡ < 1` exactly when `φ > φ̄`; for `φ > φ̄` this is the printed claim. `σˡ` ranges over
`[0, 1]`. Claim 3 (B) assumes `ρ > 0` and `φ > 1`. -/
theorem claim_3_B2_unique_crossing (γ ρ φ : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hφ : 1 < φ) (hρbar : rhoBar γ < ρ) (hφbar : phiBar γ ρ ≤ φ) :
    ∃! σdd : ℝ, (0 < σdd ∧ σdd ≤ 1) ∧ gl γ ρ φ (1, σdd) = gh γ ρ φ (1, σdd) ∧
      (∀ σl : ℝ, 0 ≤ σl → σl ≤ σdd → gh γ ρ φ (1, σl) ≤ gl γ ρ φ (1, σl)) ∧
      (∀ σl : ℝ, σdd < σl → σl ≤ 1 → gl γ ρ φ (1, σl) < gh γ ρ φ (1, σl)) ∧
      (σdd < 1 ↔ phiBar γ ρ < φ) := by sorry

end AnalystRanking.Revelation
