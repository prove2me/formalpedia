-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_claim_3_B1_gl_gt_gh
-- name    : AnalystRanking.Revelation.claim_3_B1_gl_gt_gh
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:48:05.254548+00:00
-- url     : https://prove2.me/theorems/a51f6dee-6516-458c-bc67-bba9c4c4e925
-- title:
--   Claim 3 (B.1): $g_l(1,\sigma^l)>g_h(1,\sigma^l)$ at low correlation or low convexity
-- statement:
--   Let $\gamma\in(\tfrac12,1)$, $\rho\in(0,1]$ and $\varphi>1$, with $g_l=\tfrac{\gamma}{1-\gamma}\Psi^l_i$ and $g_h=\tfrac{1-\gamma}{\gamma}\Psi^h_i$ ((B.5a)–(B.5b)). If $\rho\le\bar\rho$, or $\rho>\bar\rho$ and $1<\varphi<\bar\varphi$, then
--   $$g_l(1,\sigma^l)>g_h(1,\sigma^l)\qquad\text{for every }\sigma^l\in[0,1].$$
--
--   By (B.31), this makes the high-signal type strictly prefer truth-telling whenever the low-signal type is indifferent, which yields the semi-separating equilibria of Proposition 3 (A.1).
--
--   Differences from the source: none.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 3 (B.1), with (B.5a)–(B.5b), p. 34

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_gl
import Definitions.Def_AnalystRanking_Revelation_gh
import Definitions.Def_AnalystRanking_Revelation_rhoBar
import Definitions.Def_AnalystRanking_Revelation_phiBar

namespace AnalystRanking.Revelation

/-- **Claim 3 (B.1): `g_l(1, σˡ) > g_h(1, σˡ)` at low correlation or low convexity.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 3 (B.1), p. 34: "Suppose `ρ > 0` and `φ > 1`. If either `ρ ⩽ ρ̄`, or `ρ > ρ̄` and
`1 < φ < φ̄`, then `g_l(1, σˡ) > g_h(1, σˡ)` for any `σˡ ∈ [0, 1]`", with `g_l`, `g_h` of
(B.5a)–(B.5b) and `ρ̄`, `φ̄` of (B.3)–(B.4).

**Formalization Note.** `φ̄` is evaluated only under `ρ > ρ̄` (the disjunction guards it). -/
theorem claim_3_B1_gl_gt_gh (γ ρ φ : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hφ : 1 < φ) (hreg : ρ ≤ rhoBar γ ∨ (rhoBar γ < ρ ∧ φ < phiBar γ ρ)) :
    ∀ σl : ℝ, 0 ≤ σl → σl ≤ 1 → gh γ ρ φ (1, σl) < gl γ ρ φ (1, σl) := by sorry

end AnalystRanking.Revelation
