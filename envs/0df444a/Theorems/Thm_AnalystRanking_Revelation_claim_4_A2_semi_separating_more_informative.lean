-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_claim_4_A2_semi_separating_more_informative
-- name    : AnalystRanking.Revelation.claim_4_A2_semi_separating_more_informative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:49:22.220562+00:00
-- url     : https://prove2.me/theorems/7ea26204-ff61-4cdd-b060-8c8180d26445
-- title:
--   Claim 4 (A.2): an equilibrium $(1,\sigma^l)$ dominates any two-sided mixing equilibrium
-- statement:
--   Standing assumptions (§2): $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$, $q\in(0,1)$, and rank payoffs $w_1>w_0>w_2$ with convexity $\varphi=(w_1-w_0)/(w_0-w_2)$. Suppose $\varphi>1$ and $\rho>0$. If $(1,a)$ and $(b,c)$ are both equilibria under competition (Definition 1) with $a,b,c\in(0,1)$, then
--   $$b\le1\quad\text{and}\quad c\le a,$$
--   that is, $(1,a)$ is at least as informative as $(b,c)$ in the order of Definition 2.
--
--   This lets Proposition 3 discard two-sided mixing whenever a one-sided semi-separating equilibrium exists.
--
--   Differences from the source:
--   - encoding: signals {h,l}, forecasts {ĥ,l̂}, states {H,L}; strategy (σh, σl); payoffs w1 > w0 > w2 of (3) → Bool with true the high value; σ : ℝ × ℝ; the payoff triple (w1, w0, w2) with φ = phiConvexity w1 w0 w2; reason: Lean convention; same instances
--   - reading: display before (1), p. 7: Pr(si, sj | ω) = 2(1 − ρ)γ(1 − γ) if si ≠ sj → (1 − ρ)γ(1 − γ) for each ordered discordant pair, per (1)–(2); reason: the printed value is the probability of the event si ≠ sj; per ordered pair only (1)–(2) sum to 1
--   - reading: ℰ = the set of all equilibria (Definition 2), with symmetric equilibria and σh ⩾ 1 − σl (p. 9) → IsCompEq / IsBenchEq: symmetric σ ∈ [0,1]² with σh ≥ 1 − σl, each signal type best-responding against every mixed deviation, Bayes beliefs; reason: the paper restricts attention to these profiles on p. 9 and calls them the equilibria
--   - reading: 'more informative' → coordinatewise at least as large (b ≤ 1 ∧ c ≤ a); reason: the order of Definition 2, p. 10
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 4 (A.2), p. 35; proof, p. 38

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_IsCompEq
import Definitions.Def_AnalystRanking_Revelation_phiConvexity

namespace AnalystRanking.Revelation

/-- **Claim 4 (A.2): `σʰ = 1` semi-separation dominates two-sided mixing.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 4 (A.2), p. 35: "Suppose `φ > 1`. … If `ρ > 0`, then an equilibrium with `σʰ = 1`,
`σˡ ∈ (0, 1)`, if it exists, will always be more informative than an equilibrium with
`σʰ ∈ (0, 1)`, `σˡ ∈ (0, 1)`."

**Formalization Note.** "More informative" is the coordinatewise order of Definition 2 (p. 10):
`σʰ` and `σˡ` both at least as large. Equilibria are `IsCompEq` (Definition 1 with the p. 9
restriction). -/
theorem claim_4_A2_semi_separating_more_informative (γ ρ q w1 w0 w2 : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hw20 : w2 < w0) (hw01 : w0 < w1) (hφ : 1 < phiConvexity w1 w0 w2) (hρ : 0 < ρ) :
    ∀ a b c : ℝ, 0 < a → a < 1 → 0 < b → b < 1 → 0 < c → c < 1 →
      IsCompEq w1 w0 w2 q γ ρ (1, a) → IsCompEq w1 w0 w2 q γ ρ (b, c) → b ≤ 1 ∧ c ≤ a := by sorry

end AnalystRanking.Revelation
