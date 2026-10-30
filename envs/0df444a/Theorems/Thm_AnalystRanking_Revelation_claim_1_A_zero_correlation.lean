-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_claim_1_A_zero_correlation
-- name    : AnalystRanking.Revelation.claim_1_A_zero_correlation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:45:03.24753+00:00
-- url     : https://prove2.me/theorems/1842ac64-b8b2-423a-9363-a9b101c305dc
-- title:
--   Claim 1 (A): with $\rho=0$, separation is a best reply on $[1-\gamma,\gamma]$
-- statement:
--   Standing assumptions (§2): $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$, $q\in(0,1)$, and rank payoffs $w_1>w_0>w_2$ with convexity $\varphi=(w_1-w_0)/(w_0-w_2)$. Suppose the signals are conditionally independent, $\rho=0$, and the other analyst separates, $\sigma=(1,1)$. Then
--   $$\Delta U^h_i(1,1,q)\ge0\ \text{ if } q\ge1-\gamma,\qquad \Delta U^l_i(1,1,q)\ge0\ \text{ if } q\le\gamma .$$
--
--   With independent signals the ranking incentive cannot be exploited, so truth-telling is optimal exactly as in the benchmark.
--
--   Differences from the source:
--   - encoding: signals {h,l}, forecasts {ĥ,l̂}, states {H,L}; strategy (σh, σl); payoffs w1 > w0 > w2 of (3) → Bool with true the high value; σ : ℝ × ℝ; the payoff triple (w1, w0, w2) with φ = phiConvexity w1 w0 w2; reason: Lean convention; same instances
--   - reading: display before (1), p. 7: Pr(si, sj | ω) = 2(1 − ρ)γ(1 − γ) if si ≠ sj → (1 − ρ)γ(1 − γ) for each ordered discordant pair, per (1)–(2); reason: the printed value is the probability of the event si ≠ sj; per ordered pair only (1)–(2) sum to 1
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 1 (A), p. 33

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_dUh
import Definitions.Def_AnalystRanking_Revelation_dUl

namespace AnalystRanking.Revelation

/-- **Claim 1 (A): with uncorrelated signals truth-telling is a best reply to separation.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 1 (A), p. 33: "If `ρ = 0`, then `ΔUʰ_i(1, 1, q ⩾ 1 − γ) ⩾ 0` and
`ΔUˡ_i(1, 1, q ⩽ γ) ⩾ 0`."

**Formalization Note.** `ΔUʰ`, `ΔUˡ` are computed from the primitives (`dUh`, `dUl`), at the other
analyst's strategy `(1, 1)`; the payoffs are any `w₁ > w₀ > w₂`. -/
theorem claim_1_A_zero_correlation (γ ρ q w1 w0 w2 : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hw20 : w2 < w0) (hw01 : w0 < w1) (hρ : ρ = 0) :
    (1 - γ ≤ q → 0 ≤ dUh w1 w0 w2 q γ ρ (1, 1)) ∧ (q ≤ γ → 0 ≤ dUl w1 w0 w2 q γ ρ (1, 1)) := by sorry

end AnalystRanking.Revelation
