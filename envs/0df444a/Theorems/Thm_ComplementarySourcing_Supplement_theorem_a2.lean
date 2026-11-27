-- Prove2me | Theorems.Thm_ComplementarySourcing_Supplement_theorem_a2
-- name    : ComplementarySourcing.Supplement.theorem_a2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:50:39.595321+00:00
-- url     : https://prove2.me/theorems/b0ac4bde-40da-59cc-908a-728b24c6d1f6
-- title:
--   Theorem A2 — with known constant market appetite and endogenous wholesale price, $r\mu\ge2\epsilon_0$ reverses the first-mover disadvantage for both firms
-- statement:
--   Suppose the market appetite is known and constant, $\epsilon\equiv\epsilon_0>0$, and the first mover sets the wholesale price along with its effort. Let $\mu>0$, $\alpha\ge0$, and suppose $r\mu\ge2\epsilon_0$. Then, for every equilibrium of Model (M) and of Model (S), the first-mover disadvantage is reversed for both the manufacturer and the supplier:
--
--   $$\pi_m^{M*}>\pi_m^{S*}\qquad\text{and}\qquad\pi_s^{S*}>\pi_s^{M*}.$$
--
--   With a known, low market appetite, the demand cap prevents the second mover from free riding, whatever the complementarity.
--
--   **Formalization Note** The constant-risk models are the mission's Bernoulli Models (M) and (S) at $\sigma=0$, whose two realizations both equal $\epsilon_0$.
--
--   Differences from the source:
--   - reading: µ is "a scaling parameter for market size" (p.7) → 0 < μ; reason: a market-size scale is positive; at µ = 0 every demand is 0
--   - encoding: the optimal profits π^{M∗}, π^{S∗} of the two models → the leader's and follower's payoffs at every equilibrium of each model; reason: the page's optimum is determined by backward induction; quantifying over all equilibria changes no instance where it is unique
--   - encoding: the second mover's best response x*(·) → an arbitrary follower strategy s with IsFollowerStrategy; reason: the best response as a map from the leader's move (and the state) to an effort; its values are best responses at every feasible move
--   - reading: ϵ0, the expected market taste/appetite → 0 < ε₀; reason: at ϵ0 = 0 every demand and profit is 0 and the strict reversal fails
--   - encoding: ϵ ≡ ϵ0 → ModelM.game μ α r ε₀ 0 and ModelS.game μ α r ε₀ 0 (Bernoulli models at σ = 0); reason: both realizations are ϵ0 with probabilities ½, ½, so the law is the constant ϵ0 (the page's own remark, p.18)
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), §A3, p.A15; Theorem A2, p.A19

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame_IsEquilibrium
import Definitions.Def_ComplementarySourcing_ModelM_game
import Definitions.Def_ComplementarySourcing_ModelM_supplierProfit
import Definitions.Def_ComplementarySourcing_ModelS_game
import Definitions.Def_ComplementarySourcing_ModelS_manufacturerProfit

namespace ComplementarySourcing.Supplement

/-- **Theorem A2** (constant market risk, endogenous wholesale price). Suppose the market appetite
is known and constant, `ϵ ≡ ϵ₀`, and `rµ ≥ 2ϵ₀`. The first-mover disadvantage is reversed for
both the manufacturer and the supplier: `π^{M∗}_m > π^{S∗}_m` and `π^{S∗}_s > π^{M∗}_s`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), §A3, p.A15 (PDF 43), and Theorem A2, p.A19 (PDF 47).

**Formalization Note.** The constant-risk models are the mission's Bernoulli Models (M) and (S)
at `σ = 0` (both realizations equal `ϵ₀`, the page's "special case of the Bernoulli distribution
when σ = 0", p.18). The conclusion holds for every equilibrium of each model. `0 < ϵ₀` is the
reading of a market appetite: at `ϵ₀ = 0` every profit is `0`. -/
theorem theorem_a2 {μ α r ε₀ xM wM xS wS : ℝ} {sM sS : ℝ × ℝ → ℝ → ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hε₀ : 0 < ε₀) (hr : r * μ ≥ 2 * ε₀)
    (hM : (ModelM.game μ α r ε₀ 0).IsEquilibrium sM (xM, wM))
    (hS : (ModelS.game μ α r ε₀ 0).IsEquilibrium sS (xS, wS)) :
    ModelM.manufacturerProfit μ α r ε₀ 0 xM wM (sM (xM, wM)) >
        ModelS.manufacturerProfit μ α r ε₀ 0 xS wS (sS (xS, wS)) ∧
      ModelS.supplierProfit μ α ε₀ 0 xS wS (sS (xS, wS)) >
        ModelM.supplierProfit μ α ε₀ 0 xM wM (sM (xM, wM)) := by sorry

end ComplementarySourcing.Supplement
