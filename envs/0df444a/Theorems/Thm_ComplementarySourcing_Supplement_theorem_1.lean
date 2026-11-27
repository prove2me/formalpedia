-- Prove2me | Theorems.Thm_ComplementarySourcing_Supplement_theorem_1
-- name    : ComplementarySourcing.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:47:31.659959+00:00
-- url     : https://prove2.me/theorems/dd67e220-3213-55e0-8556-709e654b5ad8
-- title:
--   Theorem 1 — without market risk, endogenous pricing reverses the first-mover disadvantage for $\alpha r\mu\le0.46$, keeps it for $1\le\alpha r\mu\le1.08$, and makes it zero for $\alpha r\mu\ge\sqrt2$
-- statement:
--   Consider the two complementary-sourcing models **without market risk** ($\epsilon\to\infty$): in Model (M) the manufacturer chooses its effort and the wholesale price $w\in[0,r]$ first and the supplier then chooses its effort; in Model (S) the roles are swapped. Demand is $\mu(x_m+x_s+\alpha x_mx_s)$, efforts cost $\tfrac12x^2$, $r>0$ is the unit profit, $\mu>0$, $\alpha\ge0$. Write $\pi_m^{M*},\pi_s^{M*}$ and $\pi_m^{S*},\pi_s^{S*}$ for the two firms' optimal profits in Models (M) and (S).
--
--   1. If $\alpha r\mu\le0.46$, the first-mover disadvantage is reversed:
--   $$\pi_m^{M*}-\pi_m^{S*}=\pi_s^{S*}-\pi_s^{M*}>0 .$$
--   2. If $1\le\alpha r\mu\le1.08$, it persists:
--   $$\pi_m^{M*}-\pi_m^{S*}=\pi_s^{S*}-\pi_s^{M*}<0 .$$
--   3. If $\alpha r\mu\ge\sqrt2$, it is zero: no finite equilibrium exists, and in both models every firm's optimal profit is $+\infty$. Precisely, for any best-response strategies of the second movers, each first mover's supremal profit is $+\infty$, and along any feasible first-mover moves whose profit tends to $+\infty$, the second mover's profit tends to $+\infty$ as well.
--
--   Parts 1 and 2 hold for every equilibrium of each model.
--
--   The theorem shows that, without risk, the first mover's pricing power reverses the classical first-mover disadvantage only when complementarity is weak.
--
--   **Formalization Note** Part 3 is the regime of Proposition 1(1), where the optimal efforts are $+\infty$; the printed zero difference is a difference of infinite values, read here as all four optimal profits being $+\infty$ (the proof: "the two models are essentially identical").
--
--   Differences from the source:
--   - reading: r, "the unit profit for each product sold" (p.7) → 0 < r; reason: a unit profit is positive; at r = 0 every profit is 0 and part 1's strict inequality fails
--   - reading: µ is "a scaling parameter for market size" (p.7) → 0 < μ; reason: a market-size scale is positive; at µ = 0 every demand is 0
--   - encoding: the optimal profits π^{M∗}, π^{S∗} of the two models → the leader's and follower's payoffs at every equilibrium of each model; reason: the page's optimum is determined by backward induction; quantifying over all equilibria changes no instance where it is unique
--   - encoding: the second mover's best response x*(·) → an arbitrary follower strategy s with IsFollowerStrategy; reason: the best response as a map from the leader's move (and the state) to an effort; its values are best responses at every feasible move
--   - encoding: no market risk, ϵ → ∞ → uncapped demand µ(x_m + x_s + αx_mx_s) and a single state; reason: the page's benchmark; the cap min{u, ϵ} never binds
--   - reading: part 3: "π^{M∗}_m − π^{S∗}_m = π^{S∗}_s − π^{M∗}_s = 0" with x^M_m = x^S_s = +∞ (Proposition 1(1), proof p.A11) → each leader's EReal supremum of profit over feasible moves is ⊤, and along feasible leader moves whose profit tends to +∞ the follower's profit tends to +∞, in both models; reason: no finite equilibrium exists and a difference of infinite profits is undefined; the proof says the two models are essentially identical with all efforts infinite, i.e. all four optimal profits are +∞
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), Theorem 1, p.11; proof pp.A9–A11

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame_IsEquilibrium
import Definitions.Def_ComplementarySourcing_Supplement_NoRiskM_game
import Definitions.Def_ComplementarySourcing_Supplement_NoRiskS_game

namespace ComplementarySourcing.Supplement

open Filter

/-- **Theorem 1** (First Mover Disadvantage: No Market Risk). Comparing Model (M) with Model (S)
without market risk:
1. if `αrµ ≤ 0.46`, then `π^{M∗}_m − π^{S∗}_m = π^{S∗}_s − π^{M∗}_s > 0`;
2. if `1 ≤ αrµ ≤ 1.08`, then `π^{M∗}_m − π^{S∗}_m = π^{S∗}_s − π^{M∗}_s < 0`;
3. if `αrµ ≥ √2`, the first-mover disadvantage is zero: every profit is `+∞` in both models.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Theorem 1, p.11 (PDF 11); proof pp.A9–A11 (PDF 37–39).

**Formalization Note.** Parts 1–2 hold for every equilibrium `(sM, xM, wM)` of Model (M) and
every equilibrium `(sS, xS, wS)` of Model (S); `π^{M∗}_s` is the follower's payoff at the
equilibrium leader move. Part 3 is the regime of Proposition 1(1), where efforts are `+∞` and no
finite equilibrium exists, so the printed `π^M_m − π^S_m = 0` is a difference of infinite values.
It is read as: for all follower strategies `sM`, `sS`, each leader's optimal value (an `EReal`
supremum over feasible moves) is `⊤`, and along every sequence of feasible leader moves whose
leader profit tends to `+∞` the follower's profit also tends to `+∞`. `0 < r` is the reading of
"unit profit": at `r = 0` every profit is `0` and part 1's strict inequality fails. -/
theorem theorem_1 {μ α r : ℝ} (hμ : 0 < μ) (hα : 0 ≤ α) (hr : 0 < r) :
    (∀ (sM sS : ℝ × ℝ → Unit → ℝ) (xM wM xS wS : ℝ),
        (Supplement.NoRiskM.game μ α r).IsEquilibrium sM (xM, wM) →
        (Supplement.NoRiskS.game μ α r).IsEquilibrium sS (xS, wS) →
        α * r * μ ≤ 0.46 →
          (Supplement.NoRiskM.game μ α r).leaderPayoff (xM, wM) (sM (xM, wM)) -
                (Supplement.NoRiskS.game μ α r).followerPayoff (xS, wS) () (sS (xS, wS) ()) =
              (Supplement.NoRiskS.game μ α r).leaderPayoff (xS, wS) (sS (xS, wS)) -
                (Supplement.NoRiskM.game μ α r).followerPayoff (xM, wM) () (sM (xM, wM) ()) ∧
            (Supplement.NoRiskM.game μ α r).leaderPayoff (xM, wM) (sM (xM, wM)) -
                (Supplement.NoRiskS.game μ α r).followerPayoff (xS, wS) () (sS (xS, wS) ()) > 0) ∧
    (∀ (sM sS : ℝ × ℝ → Unit → ℝ) (xM wM xS wS : ℝ),
        (Supplement.NoRiskM.game μ α r).IsEquilibrium sM (xM, wM) →
        (Supplement.NoRiskS.game μ α r).IsEquilibrium sS (xS, wS) →
        1 ≤ α * r * μ → α * r * μ ≤ 1.08 →
          (Supplement.NoRiskM.game μ α r).leaderPayoff (xM, wM) (sM (xM, wM)) -
                (Supplement.NoRiskS.game μ α r).followerPayoff (xS, wS) () (sS (xS, wS) ()) =
              (Supplement.NoRiskS.game μ α r).leaderPayoff (xS, wS) (sS (xS, wS)) -
                (Supplement.NoRiskM.game μ α r).followerPayoff (xM, wM) () (sM (xM, wM) ()) ∧
            (Supplement.NoRiskM.game μ α r).leaderPayoff (xM, wM) (sM (xM, wM)) -
                (Supplement.NoRiskS.game μ α r).followerPayoff (xS, wS) () (sS (xS, wS) ()) < 0) ∧
    (Real.sqrt 2 ≤ α * r * μ →
      ∀ sM sS : ℝ × ℝ → Unit → ℝ,
        (Supplement.NoRiskM.game μ α r).IsFollowerStrategy sM →
        (Supplement.NoRiskS.game μ α r).IsFollowerStrategy sS →
          (⨆ a : {a // a ∈ (Supplement.NoRiskM.game μ α r).leaderFeasible},
              (((Supplement.NoRiskM.game μ α r).leaderPayoff a.1 (sM a.1) : ℝ) : EReal)) = ⊤ ∧
          (⨆ a : {a // a ∈ (Supplement.NoRiskS.game μ α r).leaderFeasible},
              (((Supplement.NoRiskS.game μ α r).leaderPayoff a.1 (sS a.1) : ℝ) : EReal)) = ⊤ ∧
          (∀ u : ℕ → ℝ × ℝ, (∀ n, u n ∈ (Supplement.NoRiskM.game μ α r).leaderFeasible) →
            Tendsto (fun n => (Supplement.NoRiskM.game μ α r).leaderPayoff (u n) (sM (u n)))
                atTop atTop →
              Tendsto (fun n =>
                  (Supplement.NoRiskM.game μ α r).followerPayoff (u n) () (sM (u n) ()))
                atTop atTop) ∧
          (∀ u : ℕ → ℝ × ℝ, (∀ n, u n ∈ (Supplement.NoRiskS.game μ α r).leaderFeasible) →
            Tendsto (fun n => (Supplement.NoRiskS.game μ α r).leaderPayoff (u n) (sS (u n)))
                atTop atTop →
              Tendsto (fun n =>
                  (Supplement.NoRiskS.game μ α r).followerPayoff (u n) () (sS (u n) ()))
                atTop atTop)) := by sorry

end ComplementarySourcing.Supplement
