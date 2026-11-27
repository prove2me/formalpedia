-- Prove2me | Theorems.Thm_ComplementarySourcing_Supplement_theorem_4
-- name    : ComplementarySourcing.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:49:00.371224+00:00
-- url     : https://prove2.me/theorems/b6bf8c58-1e78-4965-a3d8-7aa015c7bccb
-- title:
--   Theorem 4 — under persistent symmetric Bernoulli risk and equal margins, the first-mover disadvantage is reversed below $\mu(4-\alpha\mu)/(2-\alpha\mu)^2$ and preserved above
-- statement:
--   Suppose the second mover faces the same **persistent** market risk as the first mover: neither observes the market taste before investing. Let $\epsilon$ be Bernoulli on $\{0,\epsilon_1\}$ with $\Pr(\epsilon=\epsilon_1)=0.5$, $\epsilon_1=2\epsilon_0>0$, and let the margins be equal, normalized $r=2$, $w=1$. Let $\mu>0$, $\alpha\ge0$. "Reversed" means $\pi_m^M>\pi_m^S$ and $\pi_s^S>\pi_s^M$; "preserved" means $\pi_m^M\le\pi_m^S$ and $\pi_s^S\le\pi_s^M$. For every equilibrium of Model (M) and of Model (S):
--
--   1. If $\epsilon_1\le\tfrac12\mu$, the first-mover disadvantage is reversed.
--   2. If $\epsilon_1>\tfrac12\mu$ and $\alpha\mu\ge2$, it is reversed.
--   3. If $\epsilon_1>\tfrac12\mu$ and $\sqrt2\le\alpha\mu<2$, it is reversed when
--   $$\tfrac12\mu<\epsilon_1<\frac{\mu(4-\alpha\mu)}{(2-\alpha\mu)^2},$$
--   and preserved when $\epsilon_1\ge\mu(4-\alpha\mu)/(2-\alpha\mu)^2$.
--
--   Persistent risk does not remove the reversal: with enough complementarity the first mover still gains by investing early.
--
--   Differences from the source:
--   - reading: µ is "a scaling parameter for market size" (p.7) → 0 < μ; reason: a market-size scale is positive; at µ = 0 every demand is 0
--   - reading: sample space {0, ϵ1 = 2ϵ0} → 0 < ε₁; reason: the support has two points and ϵ0 > 0 is a mean market taste; at ϵ1 = 0 every profit is 0 and the strict reversals fail
--   - reading: "the first-mover disadvantage is reversed" / "preserved" → π^M_m > π^S_m ∧ π^S_s > π^M_s / π^M_m ≤ π^S_m ∧ π^S_s ≤ π^M_s; reason: the proofs compare both firms ("similar proof holds for the supplier", p.A11); Theorems 2, A2, A3 state reversal for both firms; preservation is the failure of the strict comparison, as in Lemma 1's ≤
--   - encoding: the optimal profits π^{M∗}, π^{S∗} of the two models → the leader's and follower's payoffs at every equilibrium of each model; reason: the page's optimum is determined by backward induction; quantifying over all equilibria changes no instance where it is unique
--   - encoding: the second mover's best response x*(·) → an arbitrary follower strategy s with IsFollowerStrategy; reason: the best response as a map from the leader's move (and the state) to an effort; its values are best responses at every feasible move
--   - encoding: symmetric margins w = r − w, normalized r = 2 (w = 1), and Prob(ϵ = ϵ1) = 0.5 → the games at r = 2, w = 1 with law ![ε₁, 0] and probabilities ![1/2, 1/2]; reason: the page's normalization, written in as printed
--   - encoding: the second mover cannot observe realized risk → a single state; the follower maximizes its expected profit; reason: the page's π_s(x_s | x_m) = p1 w µ min{u, ϵ1} − x_s²/2
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), Theorem 4, pp.20–21; proof pp.A12–A13

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame_IsEquilibrium
import Definitions.Def_ComplementarySourcing_Supplement_PersistentM_game
import Definitions.Def_ComplementarySourcing_Supplement_PersistentS_game

namespace ComplementarySourcing.Supplement

/-- **Theorem 4** (First-Mover Disadvantage: Persistent Market Risk, Symmetric Margins). Suppose
the second mover faces the same persistent market risk as the first mover, `ϵ` is Bernoulli on
`{0, ϵ₁ = 2ϵ₀}` with `Prob(ϵ = ϵ₁) = 0.5`, and the margins are symmetric, normalized `r = 2`,
`w = 1`. Then:
1. if `ϵ₁ ≤ ½µ`, the first-mover disadvantage is reversed;
2. if `ϵ₁ > ½µ` and `αµ ≥ 2`, it is reversed;
3. if `ϵ₁ > ½µ` and `√2 ≤ αµ < 2`, it is reversed if `½µ < ϵ₁ < µ(4 − αµ)/(2 − αµ)²` and
   preserved if `ϵ₁ ≥ µ(4 − αµ)/(2 − αµ)²`.
"Reversed" is `π^M_m > π^S_m ∧ π^S_s > π^M_s`, "preserved" `π^M_m ≤ π^S_m ∧ π^S_s ≤ π^M_s`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Theorem 4, pp.20–21 (PDF 20–21); proof pp.A12–A13 (PDF 40–41).

**Formalization Note.** The page's normalization `r = 2`, `w = 1` (equal margins `w = r − w`) is
written in: the games are taken at `r = 2`, `w = 1`, law `ϵ = ![ϵ₁, 0]`, `p = ![½, ½]`. The conclusion
holds for every equilibrium of each model. `0 < ϵ₁` is the reading of the two-point support
(`ϵ₀ > 0`): at `ϵ₁ = 0` every profit is `0` and part 1 fails. -/
theorem theorem_4 {μ α ε₁ xM xS : ℝ} {sM sS : ℝ → Unit → ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hε₁ : 0 < ε₁)
    (hM : (Supplement.PersistentM.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).IsEquilibrium sM xM)
    (hS : (Supplement.PersistentS.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).IsEquilibrium sS xS) :
    (ε₁ ≤ 1 / 2 * μ →
      (Supplement.PersistentM.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).leaderPayoff xM (sM xM) >
          (Supplement.PersistentS.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).followerPayoff xS ()
            (sS xS ()) ∧
        (Supplement.PersistentS.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).leaderPayoff xS (sS xS) >
          (Supplement.PersistentM.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).followerPayoff xM ()
            (sM xM ())) ∧
    (1 / 2 * μ < ε₁ → 2 ≤ α * μ →
      (Supplement.PersistentM.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).leaderPayoff xM (sM xM) >
          (Supplement.PersistentS.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).followerPayoff xS ()
            (sS xS ()) ∧
        (Supplement.PersistentS.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).leaderPayoff xS (sS xS) >
          (Supplement.PersistentM.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).followerPayoff xM ()
            (sM xM ())) ∧
    (1 / 2 * μ < ε₁ → Real.sqrt 2 ≤ α * μ → α * μ < 2 →
      (ε₁ < μ * (4 - α * μ) / (2 - α * μ) ^ 2 →
        (Supplement.PersistentM.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).leaderPayoff xM (sM xM) >
            (Supplement.PersistentS.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).followerPayoff xS ()
              (sS xS ()) ∧
          (Supplement.PersistentS.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).leaderPayoff xS (sS xS) >
            (Supplement.PersistentM.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).followerPayoff xM ()
              (sM xM ())) ∧
      (μ * (4 - α * μ) / (2 - α * μ) ^ 2 ≤ ε₁ →
        (Supplement.PersistentM.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).leaderPayoff xM (sM xM) ≤
            (Supplement.PersistentS.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).followerPayoff xS ()
              (sS xS ()) ∧
          (Supplement.PersistentS.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).leaderPayoff xS (sS xS) ≤
            (Supplement.PersistentM.game μ α 2 1 ![ε₁, 0] ![1 / 2, 1 / 2]).followerPayoff xM ()
              (sM xM ()))) := by sorry

end ComplementarySourcing.Supplement
