-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_proposition_3_A1_most_informative
-- name    : AnalystRanking.Revelation.proposition_3_A1_most_informative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:51:21.621745+00:00
-- url     : https://prove2.me/theorems/305dee25-5d6a-4621-9fe3-1a0d476753e3
-- title:
--   Proposition 3 (A.1): most informative equilibrium for convex payoffs at low correlation or low convexity
-- statement:
--   Standing assumptions (§2): $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$, $q\in(0,1)$, and rank payoffs $w_1>w_0>w_2$ with convexity $\varphi=(w_1-w_0)/(w_0-w_2)$. Suppose $\rho>0$, $\varphi>1$, and either $\rho\le\bar\rho$ or ($\rho>\bar\rho$ and $\varphi<\bar\varphi$). Then the most informative equilibrium exists for every $q\in(0,1)$ and is:
--
--   1. $\sigma^h=1=\sigma^l$ for $q\in[1-\check q_{\min},\check q_{\min}]$;
--   2. $(\check\sigma^h(q),1)$ with $\check\sigma^h(q)\in(0,1)$ for $q\in(1-\check q_{\max},1-\check q_{\min})$, and $(1,\check\sigma^l(q))$ with $\check\sigma^l(q)\in(0,1)$ for $q\in(\check q_{\min},\check q_{\max})$;
--   3. pooling, $\sigma^h=1-\sigma^l$, for $q\in(0,1-\check q_{\max}]\cup[\check q_{\max},1)$.
--
--   Here "most informative" is Definition 2 over the competition equilibria of Definition 1 (with $\sigma^h\ge1-\sigma^l$), $\check q_{\max}=\varphi\gamma/(1-\gamma+\varphi\gamma)$ (B.22), $\check\sigma^l$ is (B.30) and $\check\sigma^h(q)=\check\sigma^l(1-q)$ (B.42). Part 2 is where competition makes the analyst with the less likely signal understate it.
--
--   Differences from the source:
--   - encoding: signals {h,l}, forecasts {ĥ,l̂}, states {H,L}; strategy (σh, σl); payoffs w1 > w0 > w2 of (3) → Bool with true the high value; σ : ℝ × ℝ; the payoff triple (w1, w0, w2) with φ = phiConvexity w1 w0 w2; reason: Lean convention; same instances
--   - reading: display before (1), p. 7: Pr(si, sj | ω) = 2(1 − ρ)γ(1 − γ) if si ≠ sj → (1 − ρ)γ(1 − γ) for each ordered discordant pair, per (1)–(2); reason: the printed value is the probability of the event si ≠ sj; per ordered pair only (1)–(2) sum to 1
--   - reading: ℰ = the set of all equilibria (Definition 2), with symmetric equilibria and σh ⩾ 1 − σl (p. 9) → IsCompEq / IsBenchEq: symmetric σ ∈ [0,1]² with σh ≥ 1 − σl, each signal type best-responding against every mixed deviation, Bayes beliefs; reason: the paper restricts attention to these profiles on p. 9 and calls them the equilibria
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Proposition 3 (A.1), p. 15; (B.22), p. 42; (B.30), p. 45; (B.42), p. 50

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_IsCompEq
import Definitions.Def_AnalystRanking_Revelation_IsMostInformative
import Definitions.Def_AnalystRanking_Revelation_qminCheck
import Definitions.Def_AnalystRanking_Revelation_qmaxCheck
import Definitions.Def_AnalystRanking_Revelation_sigmaLCheck
import Definitions.Def_AnalystRanking_Revelation_rhoBar
import Definitions.Def_AnalystRanking_Revelation_phiBar
import Definitions.Def_AnalystRanking_Revelation_phiConvexity

namespace AnalystRanking.Revelation

/-- **Proposition 3 (A.1): most informative equilibrium, convex payoffs, low correlation or convexity.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Proposition 3, p. 15: "Suppose that analysts' payoff structure is not linear (`φ ≠ 1`), and
their private signals are (conditionally) positively correlated (`ρ > 0`). The most informative
(forecasting) equilibrium then exists, and is characterized as follows: A) Suppose analysts have a
convex payoff structure (`φ > 1`). A.1) If either `ρ ⩽ ρ̄`, or `ρ > ρ̄` and `1 < φ < φ̄`, then
i) `σʰ = 1 = σˡ` at `q ∈ [1 − q̌_min, q̌_min]`; ii) `σʰ = σ̌ʰ(q) ∈ (0, 1)`, `σˡ = 1` at
`q ∈ (1 − q̌_max, 1 − q̌_min)` and `σʰ = 1`, `σˡ = σ̌ˡ(q) ∈ (0, 1)` at `q ∈ (q̌_min, q̌_max)`;
iii) `σʰ = 1 − σˡ` at `q ∈ (0, 1 − q̌_max] ∪ [q̌_max, 1)`", with `σ̌ˡ` of (B.30), `q̌_max` of (B.22)
and `σ̌ʰ(q) = σ̌ˡ(1 − q)` (B.42), p. 50.

**Formalization Note.** "Most informative" is `IsMostInformative (IsCompEq …)` (Definitions 1–2);
the four cases cover every `q ∈ (0, 1)`, which is the existence claim. -/
theorem proposition_3_A1_most_informative (γ ρ q w1 w0 w2 : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hw20 : w2 < w0) (hw01 : w0 < w1) (hρ : 0 < ρ) (hφ : 1 < phiConvexity w1 w0 w2)
    (hreg : ρ ≤ rhoBar γ ∨ (rhoBar γ < ρ ∧ phiConvexity w1 w0 w2 < phiBar γ ρ)) :
    let φ := phiConvexity w1 w0 w2
    let MI := IsMostInformative (IsCompEq w1 w0 w2 q γ ρ)
    (1 - qminCheck γ ρ φ ≤ q → q ≤ qminCheck γ ρ φ → MI (1, 1)) ∧
      (1 - qmaxCheck γ φ < q → q < 1 - qminCheck γ ρ φ →
        MI (sigmaLCheck γ ρ φ (1 - q), 1) ∧
          0 < sigmaLCheck γ ρ φ (1 - q) ∧ sigmaLCheck γ ρ φ (1 - q) < 1) ∧
      (qminCheck γ ρ φ < q → q < qmaxCheck γ φ →
        MI (1, sigmaLCheck γ ρ φ q) ∧ 0 < sigmaLCheck γ ρ φ q ∧ sigmaLCheck γ ρ φ q < 1) ∧
      (q ≤ 1 - qmaxCheck γ φ ∨ qmaxCheck γ φ ≤ q → ∃ e : ℝ × ℝ, MI e ∧ e.1 = 1 - e.2) := by sorry

end AnalystRanking.Revelation
