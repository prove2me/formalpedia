-- Prove2me | Theorems.Thm_ComplementarySourcing_Supplement_theorem_5
-- name    : ComplementarySourcing.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:49:35.945205+00:00
-- url     : https://prove2.me/theorems/fa643bf7-190c-4133-bfec-7e504c6e22a8
-- title:
--   Theorem 5 (corrected: $0<\eta<1$ in part 1) — with an endogenous selling price, the first-mover disadvantage is reversed for $\mu>2\sqrt{2b}$, and at $\eta=0.5$ under a double inequality
-- statement:
--   Both firms invest before the market taste $\epsilon$ is realized; $\epsilon$ is Bernoulli on $\{0,\epsilon_1\}$ with probability $\tfrac12$ each, $\epsilon_1>0$. After the realization the manufacturer sets the selling price $r$ against the linear demand $d(x_m,x_s,\epsilon)-br$, $b>0$, choosing $r^*=d/(2b)$, and pays the supplier the fraction $\eta\in[0,1]$ of the price. Let $\mu>0$, $\alpha\ge0$. "Reversed" means $\pi_m^M>\pi_m^S$ and $\pi_s^S>\pi_s^M$, comparing the manufacturer-first and supplier-first orders of investment. For every equilibrium of each order:
--
--   1. If $\mu>2\sqrt{2b}$ and $0<\eta<1$, the first-mover disadvantage is reversed.
--   2. Suppose $\eta=0.5$ and $\mu_0\le\mu<2\sqrt{2b}$, where $\mu_0$ is the unique value in $[0,2\sqrt{2b}]$ with $\mu_0^2+2b\mu_0-8b=0$, and suppose
--   $$(1+\alpha\epsilon_1)^2<\frac{8b}{\mu^2}<\frac{\alpha\epsilon_1(1+\alpha\epsilon_1)}{(1+\alpha\epsilon_1)-\sqrt{1+\alpha\epsilon_1}} .$$
--   Then the first-mover disadvantage is reversed.
--
--   Recourse pricing under risk can reverse the first-mover disadvantage that persists with an exogenous price and no risk.
--
--   **Formalization Note** Part 1 is printed for every $\eta\in[0,1]$. At $\eta=0$ the supplier earns nothing, never invests, and the manufacturer fills demand alone in both orders, so both firms' profits coincide across orders and the strict reversal fails (symmetrically at $\eta=1$); part 1 therefore assumes $0<\eta<1$.
--
--   Differences from the source:
--   - correction: part 1: if µ > 2√(2b), reversed, for every η ∈ [0, 1] → part 1 assumes 0 < η < 1; reason: counterexample η = 0, b = 1, µ = 3, α = 0, ϵ1 = 1: the supplier earns 0 and invests 0 in both orders, the manufacturer invests 1 in both, so π^M_m = π^S_m = 5/8 and π^S_s = π^M_s = 0; symmetric at η = 1 (DISPROOF.md)
--   - reading: µ is "a scaling parameter for market size" (p.7) → 0 < μ; reason: a market-size scale is positive; at µ = 0 every demand is 0
--   - reading: sample space {0, ϵ1 = 2ϵ0} → 0 < ε₁; reason: the support has two points and ϵ0 > 0 is a mean market taste; at ϵ1 = 0 every profit is 0 and the strict reversals fail
--   - reading: "the first-mover disadvantage is reversed" → π^M_m > π^S_m ∧ π^S_s > π^M_s; reason: the proofs compare both firms ("similar proof holds for the supplier", p.A11); Theorems 2, A2, A3 state reversal for both firms; preservation is the failure of the strict comparison, as in Lemma 1's ≤
--   - encoding: the optimal profits π^{M∗}, π^{S∗} of the two models → the leader's and follower's payoffs at every equilibrium of each model; reason: the page's optimum is determined by backward induction; quantifying over all equilibria changes no instance where it is unique
--   - encoding: the second mover's best response x*(·) → an arbitrary follower strategy s with IsFollowerStrategy; reason: the best response as a map from the leader's move (and the state) to an effort; its values are best responses at every feasible move
--   - reading: b, the slope of the linear demand function, and 0 ≤ η ≤ 1 → 0 < b, 0 ≤ η ≤ 1; reason: a downward-sloping demand; η is a fraction of the price
--   - reading: "same model setup as §4.2" with risk realized after investment, and the supplier's payoff (η/8b)d(x_m, x_s, ϵ1)² − x_s²/2 (p.A23) → law ![ε₁, 0] with probabilities ![1/2, 1/2]; no firm observes the risk before investing; reason: the factor 1/8 = ½ · 1/4 on p.A23 fixes Prob(ϵ = ϵ1) = ½
--   - reading: the first-mover disadvantage, with only the manufacturer-first order described → comparison with the supplier-first order in which the manufacturer still sets the selling price; reason: the disadvantage compares leading with following; the proof's symmetric-margin argument ("reversed iff x^M_m < x^M_s") uses this mirror order
--   - encoding: the manufacturer "sets the optimal market selling price" after the risk resolves → payoffs at the recourse price r* = d/(2b); reason: the unique optimal recourse price for b > 0 (p.A23), substituted
--   - encoding: µ0 is the unique value in [0, 2√(2b)] with µ0² + 2bµ0 − 8b = 0 → a universally quantified µ₀ satisfying 0 ≤ µ₀ ≤ 2√(2b) and µ₀² + 2bµ₀ − 8b = 0; reason: for b > 0 these conditions have exactly one solution, so no instance changes
--   - encoding: the bound αϵ1(1 + αϵ1)/((1 + αϵ1) − √(1 + αϵ1)), undefined when αϵ1 = 0 → Lean real division, which is 0 there, so the hypothesis 8b/µ² < 0 is false; reason: excludes only the case where the printed quotient is undefined (0/0); no defined instance changes
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), Theorem 5, p.23; proof p.A14; Lemma A5 and Proposition A7, pp.A24–A25

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame_IsEquilibrium
import Definitions.Def_ComplementarySourcing_Supplement_RecourseM_game
import Definitions.Def_ComplementarySourcing_Supplement_RecourseS_game

namespace ComplementarySourcing.Supplement

/-- **Theorem 5** (Reversal of First-Mover Disadvantage: Endogenous Selling Price), corrected.
Both firms invest before the risk `ϵ` (Bernoulli on `{0, ϵ₁}`, probability ½ each, §4.2–§4.3)
resolves; the manufacturer then sets the selling price `r` against demand `d − br`, and the
supplier receives the fraction `η` of the price.
1. If `µ > 2√(2b)` (and `0 < η < 1`), the first-mover disadvantage is reversed.
2. Suppose `η = 0.5` and `µ₀ ≤ µ < 2√(2b)`, where `µ₀` is the unique value in `[0, 2√(2b)]` with
   `µ₀² + 2bµ₀ − 8b = 0`, and `(1 + αϵ₁)² < 8b/µ² < αϵ₁(1 + αϵ₁)/((1 + αϵ₁) − √(1 + αϵ₁))`. Then the
   first-mover disadvantage is reversed.
"Reversed" is `π^M_m > π^S_m ∧ π^S_s > π^M_s`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Theorem 5, p.23 (PDF 23); proof p.A14 (PDF 42), Lemma A5 and Proposition A7, pp.A24–A25
(PDF 52–53).

**Formalization Note.** The conclusion holds for every equilibrium `(sM, xM)` of the
manufacturer-first model and `(sS, xS)` of the supplier-first model, law `![ϵ₁, 0]`, `![½, ½]`.
Part 1 is printed for every `η ∈ [0, 1]`; at `η = 0` (and `η = 1`) one firm earns nothing, both
orders have the other firm fill demand alone, and the two firms' profits coincide across orders, so
the strict reversal fails; part 1 here assumes `0 < η < 1`. `µ₀` is a binder pinned by the
printed conditions, which determine it uniquely for `b > 0`. `0 < ϵ₁` is the reading of the
two-point support (`ϵ₀ > 0`). -/
theorem theorem_5 {μ α b η ε₁ xM xS : ℝ} {sM sS : ℝ → Unit → ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hb : 0 < b) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hε₁ : 0 < ε₁)
    (hM : (Supplement.RecourseM.game μ α b η ![ε₁, 0] ![1 / 2, 1 / 2]).IsEquilibrium sM xM)
    (hS : (Supplement.RecourseS.game μ α b η ![ε₁, 0] ![1 / 2, 1 / 2]).IsEquilibrium sS xS) :
    (2 * Real.sqrt (2 * b) < μ → 0 < η → η < 1 →
      (Supplement.RecourseM.game μ α b η ![ε₁, 0] ![1 / 2, 1 / 2]).leaderPayoff xM (sM xM) >
          (Supplement.RecourseS.game μ α b η ![ε₁, 0] ![1 / 2, 1 / 2]).followerPayoff xS ()
            (sS xS ()) ∧
        (Supplement.RecourseS.game μ α b η ![ε₁, 0] ![1 / 2, 1 / 2]).leaderPayoff xS (sS xS) >
          (Supplement.RecourseM.game μ α b η ![ε₁, 0] ![1 / 2, 1 / 2]).followerPayoff xM ()
            (sM xM ())) ∧
    (∀ μ₀ : ℝ, η = 0.5 →
      0 ≤ μ₀ → μ₀ ≤ 2 * Real.sqrt (2 * b) → μ₀ ^ 2 + 2 * b * μ₀ - 8 * b = 0 →
      μ₀ ≤ μ → μ < 2 * Real.sqrt (2 * b) →
      (1 + α * ε₁) ^ 2 < 8 * b / μ ^ 2 →
      8 * b / μ ^ 2 < α * ε₁ * (1 + α * ε₁) / ((1 + α * ε₁) - Real.sqrt (1 + α * ε₁)) →
        (Supplement.RecourseM.game μ α b η ![ε₁, 0] ![1 / 2, 1 / 2]).leaderPayoff xM (sM xM) >
            (Supplement.RecourseS.game μ α b η ![ε₁, 0] ![1 / 2, 1 / 2]).followerPayoff xS ()
              (sS xS ()) ∧
          (Supplement.RecourseS.game μ α b η ![ε₁, 0] ![1 / 2, 1 / 2]).leaderPayoff xS (sS xS) >
            (Supplement.RecourseM.game μ α b η ![ε₁, 0] ![1 / 2, 1 / 2]).followerPayoff xM ()
              (sM xM ())) := by sorry

end ComplementarySourcing.Supplement
