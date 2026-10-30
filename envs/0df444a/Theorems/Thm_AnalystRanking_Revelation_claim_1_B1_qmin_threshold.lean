-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_claim_1_B1_qmin_threshold
-- name    : AnalystRanking.Revelation.claim_1_B1_qmin_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:45:57.718317+00:00
-- url     : https://prove2.me/theorems/cdd4772d-773a-4fc8-9008-affbb9f67336
-- title:
--   Claim 1 (B.1): separation is a best reply exactly on $[1-q_{\min},q_{\min}]$
-- statement:
--   Standing assumptions (§2): $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$, $q\in(0,1)$, and rank payoffs $w_1>w_0>w_2$ with convexity $\varphi=(w_1-w_0)/(w_0-w_2)$. Suppose $\rho>0$ and let
--   $$q_{\min}=\gamma-\chi\left[\frac{\varphi-1}{(1-\gamma)\varphi+\gamma}\right],\qquad\chi=\rho\gamma(1-\gamma)\quad\text{(B.2)}.$$
--   Then $q_{\min}\in(0,1)$, and when the other analyst separates,
--   $$\Delta U^h_i(1,1,q)\ge0\iff q\ge1-q_{\min},\qquad \Delta U^l_i(1,1,q)\ge0\iff q\le q_{\min}.$$
--
--   Under convex payoffs $q_{\min}=\check q_{\min}<\gamma$: correlation shrinks the interval of priors on which a separating equilibrium exists.
--
--   Differences from the source:
--   - encoding: signals {h,l}, forecasts {ĥ,l̂}, states {H,L}; strategy (σh, σl); payoffs w1 > w0 > w2 of (3) → Bool with true the high value; σ : ℝ × ℝ; the payoff triple (w1, w0, w2) with φ = phiConvexity w1 w0 w2; reason: Lean convention; same instances
--   - reading: display before (1), p. 7: Pr(si, sj | ω) = 2(1 − ρ)γ(1 − γ) if si ≠ sj → (1 − ρ)γ(1 − γ) for each ordered discordant pair, per (1)–(2); reason: the printed value is the probability of the event si ≠ sj; per ordered pair only (1)–(2) sum to 1
--   - generalization: ΔUh_i(1,1,q) ⩾ 0 if q ⩾ 1 − qmin, and ΔUl_i(1,1,q) ⩾ 0 if q ⩽ qmin → both as 'iff'; reason: the proof's simplification (B.7) is an equivalence and Proposition 3's proof uses the converse (ΔUl_i(1,1,q′) < 0 for q′ > q̌min); the iff specializes to the printed 'if'
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 1 (B.1), pp. 33–34, display (B.2), and its proof (B.7), p. 35

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_dUh
import Definitions.Def_AnalystRanking_Revelation_dUl
import Definitions.Def_AnalystRanking_Revelation_qminCheck
import Definitions.Def_AnalystRanking_Revelation_phiConvexity

namespace AnalystRanking.Revelation

/-- **Claim 1 (B.1): the threshold `q_min` of (B.2), stated as an equivalence.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Claim 1 (B.1), pp. 33–34: "There exists `q_min ∈ (0, 1)` such that `ΔUʰ_i(1, 1, q) ⩾ 0` if
`q ⩾ 1 − q_min`, and `ΔUˡ_i(1, 1, q) ⩾ 0` if `q ⩽ q_min`, where
`q_min = γ − χ[(φ − 1)/((1 − γ)φ + γ)]`, (B.2), where `χ = ργ(1 − γ)`." The proof (p. 35):
"Simplifying `ΔUˡ_i(1, 1, q) ⩾ 0` yields … `q ⩽ … ≡ q_min`".

**Formalization Note.** Generalization: "if" is stated as "iff", which is what the proof's
simplification shows (and what Proposition 3's proof uses: `ΔUˡ_i(1, 1, q′) < 0` for
`q′ > q̌_min`). Standing assumptions of §2 and `ρ > 0` as printed; any `w₁ > w₀ > w₂`. -/
theorem claim_1_B1_qmin_threshold (γ ρ q w1 w0 w2 : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hw20 : w2 < w0) (hw01 : w0 < w1) (hρ : 0 < ρ) :
    0 < qminCheck γ ρ (phiConvexity w1 w0 w2) ∧ qminCheck γ ρ (phiConvexity w1 w0 w2) < 1 ∧
      (0 ≤ dUh w1 w0 w2 q γ ρ (1, 1) ↔ 1 - qminCheck γ ρ (phiConvexity w1 w0 w2) ≤ q) ∧
      (0 ≤ dUl w1 w0 w2 q γ ρ (1, 1) ↔ q ≤ qminCheck γ ρ (phiConvexity w1 w0 w2)) := by sorry

end AnalystRanking.Revelation
