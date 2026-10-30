-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_proposition_3_A2_most_informative
-- name    : AnalystRanking.Revelation.proposition_3_A2_most_informative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:52:20.862428+00:00
-- url     : https://prove2.me/theorems/466427b8-f5f5-45ae-867e-21b67138e912
-- title:
--   Proposition 3 (A.2): most informative equilibrium at high correlation and convexity (corrected: interior strategy on the open interval)
-- statement:
--   Standing assumptions (§2): $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$, $q\in(0,1)$, and rank payoffs $w_1>w_0>w_2$ with convexity $\varphi=(w_1-w_0)/(w_0-w_2)$. Suppose $\varphi>1$, $\rho>\bar\rho$ and $\varphi\ge\bar\varphi$. Then there is $\ddot\sigma^l\in(0,1]$ with $g_l(1,\ddot\sigma^l)=g_h(1,\ddot\sigma^l)$ such that, with $\bar q=g_l(1,\ddot\sigma^l)/(1+g_l(1,\ddot\sigma^l))$ (B.33), for every $q\in(0,1)$ the most informative equilibrium exists and is:
--
--   1. $(\dot\sigma^h(q),\dot\sigma^l(q))$ of (B.34) for $q\in[1-\bar q,\bar q]$, with both coordinates in $(0,1)$ for $q\in(1-\bar q,\bar q)$;
--   2. $(\check\sigma^h(q),1)$ with $\check\sigma^h(q)\in(0,\ddot\sigma^l)$ for $q\in(1-\check q_{\max},1-\bar q)$, and $(1,\check\sigma^l(q))$ with $\check\sigma^l(q)\in(0,\ddot\sigma^l)$ for $q\in(\bar q,\check q_{\max})$;
--   3. pooling, $\sigma^h=1-\sigma^l$, for $q\in(0,1-\check q_{\max}]\cup[\check q_{\max},1)$.
--
--   Here "most informative" is Definition 2 over the competition equilibria of Definition 1 (with $\sigma^h\ge1-\sigma^l$), $\check q_{\max}=\varphi\gamma/(1-\gamma+\varphi\gamma)$ (B.22), $\check\sigma^l$ is (B.30) and $\check\sigma^h(q)=\check\sigma^l(1-q)$ (B.42). In this regime no prior supports full separation.
--
--   Differences from the source:
--   - correction: i) σh = σ̇h(q) ∈ (0,1), σl = σ̇l(q) ∈ (0,1) at q ∈ [1 − q̄, q̄]; σ̈l ∈ (0,1) → σ̇(q) is the most informative equilibrium on [1 − q̄, q̄]; σ̇(q) ∈ (0,1)² on (1 − q̄, q̄); σ̈l ∈ (0,1]; reason: σ̇(q̄) = (1, σ̈l) and σ̇(1 − q̄) = (σ̈l, 1) (e.g. γ = 0.75, ρ = 0.8, φ = 1.5·27/7: σ̇(q̄) = (1, 0.8139)); at φ = φ̄, σ̈l = 1, q̄ = 1/2 and σ̇(1/2) = (1,1) (Claim 3 (B.2) correction)
--   - encoding: signals {h,l}, forecasts {ĥ,l̂}, states {H,L}; strategy (σh, σl); payoffs w1 > w0 > w2 of (3) → Bool with true the high value; σ : ℝ × ℝ; the payoff triple (w1, w0, w2) with φ = phiConvexity w1 w0 w2; reason: Lean convention; same instances
--   - reading: display before (1), p. 7: Pr(si, sj | ω) = 2(1 − ρ)γ(1 − γ) if si ≠ sj → (1 − ρ)γ(1 − γ) for each ordered discordant pair, per (1)–(2); reason: the printed value is the probability of the event si ≠ sj; per ordered pair only (1)–(2) sum to 1
--   - reading: ℰ = the set of all equilibria (Definition 2), with symmetric equilibria and σh ⩾ 1 − σl (p. 9) → IsCompEq / IsBenchEq: symmetric σ ∈ [0,1]² with σh ≥ 1 − σl, each signal type best-responding against every mixed deviation, Bayes beliefs; reason: the paper restricts attention to these profiles on p. 9 and calls them the equilibria
--   - encoding: σ̈h = σ̈l (B.42) → the bound σ̌h(q) < σdd uses the single crossing σdd; reason: (B.42) states σ̈h = σ̈l
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Proposition 3 (A.2), pp. 15–16; (B.6), p. 35; (B.33), p. 46; (B.34), p. 47; (B.42), p. 50

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_IsCompEq
import Definitions.Def_AnalystRanking_Revelation_IsMostInformative
import Definitions.Def_AnalystRanking_Revelation_qminCheck
import Definitions.Def_AnalystRanking_Revelation_qmaxCheck
import Definitions.Def_AnalystRanking_Revelation_sigmaLCheck
import Definitions.Def_AnalystRanking_Revelation_rhoBar
import Definitions.Def_AnalystRanking_Revelation_phiBar
import Definitions.Def_AnalystRanking_Revelation_phiConvexity
import Definitions.Def_AnalystRanking_Revelation_gl
import Definitions.Def_AnalystRanking_Revelation_gh
import Definitions.Def_AnalystRanking_Revelation_sigmaDot

namespace AnalystRanking.Revelation

/-- **Proposition 3 (A.2): most informative equilibrium, high convexity and correlation (corrected).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Proposition 3, pp. 15–16: "… A.2) If `ρ > ρ̄` and `φ ⩾ φ̄` (high convexity, high
correlation), then i) `σʰ = σ̇ʰ(q) ∈ (0, 1)`, `σˡ = σ̇ˡ(q) ∈ (0, 1)` at `q ∈ [1 − q̄, q̄]`;
ii) `σʰ = σ̌ʰ(q) ∈ (0, σ̈ʰ)`, `σˡ = 1` at `q ∈ (1 − q̌_max, 1 − q̄)` and `σʰ = 1`,
`σˡ = σ̌ˡ(q) ∈ (0, σ̈ˡ)` at `q ∈ (q̄, q̌_max)`; iii) `σʰ = 1 − σˡ` at
`q ∈ (0, 1 − q̌_max] ∪ [q̌_max, 1)`", with `σ̇` of (B.34), `σ̌ˡ` of (B.30), `σ̌ʰ(q) = σ̌ˡ(1 − q)`,
`g_l(1, σ̈ˡ) = g_h(1, σ̈ˡ)` (B.6), `q̄ = g_l(1, σ̈ˡ)/(1 + g_l(1, σ̈ˡ))` (B.33) and `σ̈ʰ = σ̈ˡ` (B.42).

**Formalization Note.** Correction: `σ̇(q̄) = (1, σ̈ˡ)` and `σ̇(1 − q̄) = (σ̈ˡ, 1)`, so the strict
membership `σ̇(q) ∈ (0, 1)²` of i) holds on the open interval `(1 − q̄, q̄)` only; at `φ = φ̄`,
`σ̈ˡ = 1`, `q̄ = 1/2` and `σ̇(1/2) = (1, 1)` (Claim 3 (B.2) correction). The characterization
`σ̇(q)` is stated on the closed interval. The crossing `σ̈ˡ` is taken in `(0, 1]`; it is unique by
Claim 3 (B.2). -/
theorem proposition_3_A2_most_informative (γ ρ w1 w0 w2 : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1)
    (hρ1 : ρ ≤ 1) (hw20 : w2 < w0) (hw01 : w0 < w1) (hφ : 1 < phiConvexity w1 w0 w2)
    (hρbar : rhoBar γ < ρ) (hφbar : phiBar γ ρ ≤ phiConvexity w1 w0 w2) :
    let φ := phiConvexity w1 w0 w2
    ∃ σdd : ℝ, 0 < σdd ∧ σdd ≤ 1 ∧ gl γ ρ φ (1, σdd) = gh γ ρ φ (1, σdd) ∧
      let qbar := gl γ ρ φ (1, σdd) / (1 + gl γ ρ φ (1, σdd))
      ∀ q : ℝ, 0 < q → q < 1 →
        let MI := IsMostInformative (IsCompEq w1 w0 w2 q γ ρ)
        (1 - qbar ≤ q → q ≤ qbar → MI (sigmaDot γ ρ φ q)) ∧
        (1 - qbar < q → q < qbar →
          0 < (sigmaDot γ ρ φ q).1 ∧ (sigmaDot γ ρ φ q).1 < 1 ∧
            0 < (sigmaDot γ ρ φ q).2 ∧ (sigmaDot γ ρ φ q).2 < 1) ∧
        (1 - qmaxCheck γ φ < q → q < 1 - qbar →
          MI (sigmaLCheck γ ρ φ (1 - q), 1) ∧
            0 < sigmaLCheck γ ρ φ (1 - q) ∧ sigmaLCheck γ ρ φ (1 - q) < σdd) ∧
        (qbar < q → q < qmaxCheck γ φ →
          MI (1, sigmaLCheck γ ρ φ q) ∧ 0 < sigmaLCheck γ ρ φ q ∧ sigmaLCheck γ ρ φ q < σdd) ∧
        (q ≤ 1 - qmaxCheck γ φ ∨ qmaxCheck γ φ ≤ q → ∃ e : ℝ × ℝ, MI e ∧ e.1 = 1 - e.2) := by sorry

end AnalystRanking.Revelation
