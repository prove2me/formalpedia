-- Prove2me | Theorems.Thm_ComplementarySourcing_theorem_2
-- name    : ComplementarySourcing.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:09:04.628711+00:00
-- url     : https://prove2.me/theorems/962039c5-1446-46d6-b4b6-70c7f2e70c76
-- title:
--   Theorem 2, p.14 — Reversal of First Mover Disadvantage: With Market Risk
-- statement:
--   Consider Model (M), in which the manufacturer moves first, and Model (S), in which the supplier moves first, with market risk $\epsilon\in\{\epsilon_0+\sigma,\epsilon_0-\sigma\}$ of probability $\tfrac12$ each. Let $\mu>0$, $\alpha\ge0$, $\epsilon_0>0$, $\sigma\ge0$, and suppose
--
--   $$r\mu\ge3\epsilon_0+\sigma\qquad\text{and}\qquad\frac{\sigma}{\epsilon_0}\le3-2\sqrt2.$$
--
--   Then, for every equilibrium of Model (M) and every equilibrium of Model (S),
--
--   $$\pi^{M*}_m>\pi^{S*}_m\qquad\text{and}\qquad\pi^{S*}_s>\pi^{M*}_s.$$
--
--   Each firm earns strictly more as the first mover: market risk reverses the first-mover disadvantage of complementary sourcing, for every complementarity $\alpha\ge0$.
--
--   Differences from the source:
--   - reading: µ is "a scaling parameter for market size" (p.7), and the page divides by µ (p.13) → 0 < μ; reason: a market-size scale is positive; the page's formulas are undefined at µ = 0
--   - reading: 0 ≤ σ ≤ ϵ0, with σ/ϵ0 and the optimal price meaningful → 0 < ε₀; reason: at ϵ0 = 0 demand is 0 at every price, so the printed unique optimum and the ratio σ/ϵ0 lose their meaning
--   - encoding: π^{M∗}, π^{S∗} named through "the smallest index k" → every equilibrium of each model; reason: the equilibrium is unique (Propositions 2 and 3), so no instance changes
--   - encoding: the second mover's response x*(·|ϵ) → an arbitrary strategy s with IsFollowerStrategy; reason: the page's best response as a map; by Lemma 2 its values are determined on the feasible moves and the two states
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), Theorem 2, p.14; proof p.A11

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame_IsEquilibrium
import Definitions.Def_ComplementarySourcing_ModelM_game
import Definitions.Def_ComplementarySourcing_ModelM_supplierProfit
import Definitions.Def_ComplementarySourcing_ModelS_game
import Definitions.Def_ComplementarySourcing_ModelS_manufacturerProfit

namespace ComplementarySourcing

/-- **Theorem 2** (Reversal of First Mover Disadvantage: With Market Risk): if `rµ ≥ 3ϵ₀ + σ` and
`σ/ϵ₀ ≤ 3 − 2√2`, then `π^{M∗}_m > π^{S∗}_m` and `π^{S∗}_s > π^{M∗}_s`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Theorem 2, p.14 (PDF 14).

**Formalization Note.** The conclusion holds for every equilibrium `(sM, xM, wM)` of Model (M) and
every equilibrium `(sS, xS, wS)` of Model (S), for every `α ≥ 0`. `σ ≤ ϵ₀` follows from the ratio
hypothesis, and `r > 0` from the first hypothesis, so neither is a binder. `ϵ₀ > 0` is the reading
of the ratio: Lean's `σ / 0 = 0` would otherwise admit `ϵ₀ = σ = 0`, where every profit is `0`. -/
theorem theorem_2 {μ α r ε₀ σ xM wM xS wS : ℝ} {sM sS : ℝ × ℝ → ℝ → ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hε₀ : 0 < ε₀) (hσ₀ : 0 ≤ σ)
    (hr : r * μ ≥ 3 * ε₀ + σ) (hσ : σ / ε₀ ≤ 3 - 2 * Real.sqrt 2)
    (hM : (ModelM.game μ α r ε₀ σ).IsEquilibrium sM (xM, wM))
    (hS : (ModelS.game μ α r ε₀ σ).IsEquilibrium sS (xS, wS)) :
    ModelM.manufacturerProfit μ α r ε₀ σ xM wM (sM (xM, wM)) >
        ModelS.manufacturerProfit μ α r ε₀ σ xS wS (sS (xS, wS)) ∧
      ModelS.supplierProfit μ α ε₀ σ xS wS (sS (xS, wS)) >
        ModelM.supplierProfit μ α ε₀ σ xM wM (sM (xM, wM)) := by sorry

end ComplementarySourcing
