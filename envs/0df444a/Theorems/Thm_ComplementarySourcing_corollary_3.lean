-- Prove2me | Theorems.Thm_ComplementarySourcing_corollary_3
-- name    : ComplementarySourcing.corollary_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:40.147303+00:00
-- url     : https://prove2.me/theorems/b26cb959-c73c-4175-a11e-9e444fb1fce7
-- title:
--   Corollary 3, p.14 — the two models swap the firms' profits
-- statement:
--   Let $\mu>0$, $\alpha\ge0$, $\epsilon_0>0$, $0\le\sigma\le\epsilon_0$ and $r\mu\ge3\epsilon_0+\sigma$. For every equilibrium of Model (M) and every equilibrium of Model (S),
--
--   1. $\pi^{M*}_m=\pi^{S*}_s$ and $\pi^{M*}_s=\pi^{S*}_m$;
--   2. $\pi^{M*}_m+\pi^{M*}_s=\pi^{S*}_m+\pi^{S*}_s$.
--
--   The first mover's profit and the second mover's profit do not depend on which firm moves first, and the expected total supply chain profit is the same in both models.
--
--   Differences from the source:
--   - reading: no hypothesis printed; the corollary "follows from Propositions 2 and 3" → r * μ ≥ 3 * ε₀ + σ; reason: it is the hypothesis of the propositions it follows from, and without it an equilibrium need not be unique, so the second mover's profit need not be well defined
--   - reading: µ is "a scaling parameter for market size" (p.7), and the page divides by µ (p.13) → 0 < μ; reason: a market-size scale is positive; the page's formulas are undefined at µ = 0
--   - reading: 0 ≤ σ ≤ ϵ0, with σ/ϵ0 and the optimal price meaningful → 0 < ε₀; reason: at ϵ0 = 0 demand is 0 at every price, so the printed unique optimum and the ratio σ/ϵ0 lose their meaning
--   - encoding: π^{M∗}, π^{S∗} named through "the smallest index k" → every equilibrium of each model; reason: the equilibrium is unique (Propositions 2 and 3), so no instance changes
--   - encoding: the second mover's response x*(·|ϵ) → an arbitrary strategy s with IsFollowerStrategy; reason: the page's best response as a map; by Lemma 2 its values are determined on the feasible moves and the two states
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), Corollary 3, p.14; proof p.A11

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame_IsEquilibrium
import Definitions.Def_ComplementarySourcing_ModelM_game
import Definitions.Def_ComplementarySourcing_ModelM_supplierProfit
import Definitions.Def_ComplementarySourcing_ModelS_game
import Definitions.Def_ComplementarySourcing_ModelS_manufacturerProfit

namespace ComplementarySourcing

/-- **Corollary 3** (Optimal Profit Comparison): `π^{M∗}_m = π^{S∗}_s`, `π^{M∗}_s = π^{S∗}_m`, and
`π^{M∗}_m + π^{M∗}_s = π^{S∗}_m + π^{S∗}_s`, for every equilibrium of each model.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Corollary 3, p.14 (PDF 14).

**Formalization Note.** The page prints no hypothesis of its own; it "follows from Propositions 2
and 3", so their hypothesis `rµ ≥ 3ϵ₀ + σ` is the hypothesis here. -/
theorem corollary_3 {μ α r ε₀ σ xM wM xS wS : ℝ} {sM sS : ℝ × ℝ → ℝ → ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hε₀ : 0 < ε₀) (hσ₀ : 0 ≤ σ) (hσ : σ ≤ ε₀)
    (hr : r * μ ≥ 3 * ε₀ + σ)
    (hM : (ModelM.game μ α r ε₀ σ).IsEquilibrium sM (xM, wM))
    (hS : (ModelS.game μ α r ε₀ σ).IsEquilibrium sS (xS, wS)) :
    ModelM.manufacturerProfit μ α r ε₀ σ xM wM (sM (xM, wM)) =
        ModelS.supplierProfit μ α ε₀ σ xS wS (sS (xS, wS)) ∧
      ModelM.supplierProfit μ α ε₀ σ xM wM (sM (xM, wM)) =
        ModelS.manufacturerProfit μ α r ε₀ σ xS wS (sS (xS, wS)) ∧
      ModelM.manufacturerProfit μ α r ε₀ σ xM wM (sM (xM, wM)) +
          ModelM.supplierProfit μ α ε₀ σ xM wM (sM (xM, wM)) =
        ModelS.manufacturerProfit μ α r ε₀ σ xS wS (sS (xS, wS)) +
          ModelS.supplierProfit μ α ε₀ σ xS wS (sS (xS, wS)) := by sorry

end ComplementarySourcing
