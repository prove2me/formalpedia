-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_claim_5_A_no_high_type_mixing
-- name    : AnalystRanking.Revelation.claim_5_A_no_high_type_mixing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:50:17.840453+00:00
-- url     : https://prove2.me/theorems/bd90884d-5baf-4b74-a8ae-829294c80066
-- title:
--   Claim 5 (A): no equilibrium with $\sigma^h\in(0,1)$, $\sigma^l=1$ above $\check q_{\min}$
-- statement:
--   Standing assumptions (§2): $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$, $q\in(0,1)$, and rank payoffs $w_1>w_0>w_2$ with convexity $\varphi=(w_1-w_0)/(w_0-w_2)$. Suppose $\varphi>1$ and $q>q_{\min}$ (of (B.2); $q_{\min}=\gamma$ when $\rho=0$). Then for no $b\in(0,1)$ is $(b,1)$ an equilibrium under competition.
--
--   Above $\check q_{\min}$ the high-signal type strictly prefers to forecast high whenever the low-signal type tells the truth, so the only candidates are semi-separating with $\sigma^h=1$.
--
--   Differences from the source:
--   - encoding: signals {h,l}, forecasts {ĥ,l̂}, states {H,L}; strategy (σh, σl); payoffs w1 > w0 > w2 of (3) → Bool with true the high value; σ : ℝ × ℝ; the payoff triple (w1, w0, w2) with φ = phiConvexity w1 w0 w2; reason: Lean convention; same instances
--   - reading: display before (1), p. 7: Pr(si, sj | ω) = 2(1 − ρ)γ(1 − γ) if si ≠ sj → (1 − ρ)γ(1 − γ) for each ordered discordant pair, per (1)–(2); reason: the printed value is the probability of the event si ≠ sj; per ordered pair only (1)–(2) sum to 1
--   - reading: ℰ = the set of all equilibria (Definition 2), with symmetric equilibria and σh ⩾ 1 − σl (p. 9) → IsCompEq / IsBenchEq: symmetric σ ∈ [0,1]² with σh ≥ 1 − σl, each signal type best-responding against every mixed deviation, Bayes beliefs; reason: the paper restricts attention to these profiles on p. 9 and calls them the equilibria
--   - encoding: for any q > γ if ρ = 0, and for any q > q̌min if ρ > 0 → qminCheck γ ρ φ < q for every ρ ∈ [0,1]; reason: qminCheck γ 0 φ = γ, so the two cases are one statement
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 5 (A), p. 35

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_IsCompEq
import Definitions.Def_AnalystRanking_Revelation_qminCheck
import Definitions.Def_AnalystRanking_Revelation_phiConvexity

namespace AnalystRanking.Revelation

/-- **Claim 5 (A): no equilibrium with `σʰ ∈ (0, 1)`, `σˡ = 1` above `q̌_min`.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 5 (A), p. 35: "If `φ > 1`, then there cannot exist an equilibrium with `σʰ ∈ (0, 1)`,
`σˡ = 1` for any `q > γ` if `ρ = 0`, and for any `q > q̌_min` if `ρ > 0`."

**Formalization Note.** Both cases are one statement: at `ρ = 0`, `q_min = γ` by (B.2). -/
theorem claim_5_A_no_high_type_mixing (γ ρ q w1 w0 w2 : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hw20 : w2 < w0) (hw01 : w0 < w1) (hφ : 1 < phiConvexity w1 w0 w2)
    (hq : qminCheck γ ρ (phiConvexity w1 w0 w2) < q) :
    ∀ b : ℝ, 0 < b → b < 1 → ¬ IsCompEq w1 w0 w2 q γ ρ (b, 1) := by sorry

end AnalystRanking.Revelation
