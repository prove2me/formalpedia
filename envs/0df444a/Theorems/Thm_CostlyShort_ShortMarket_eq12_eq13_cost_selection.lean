-- Prove2me | Theorems.Thm_CostlyShort_ShortMarket_eq12_eq13_cost_selection
-- name    : CostlyShort.ShortMarket.eq12_eq13_cost_selection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:37.69533+00:00
-- url     : https://prove2.me/theorems/7ebe7619-f02b-4f56-91b4-bd59870aa44d
-- title:
--   (12)–(13), p. 18 — the maximizers of y ↦ y(θ₁⁽ᵖ⁾+y)⁻ over y ≥ γ, corrected; their least element is max{γ, −½θ₁⁽ᵖ⁾}
-- statement:
--   Let $\theta^{(o)}_1,\theta^{(p)}_1$ be the market prices of risk of asset 1 for the optimist and the pessimist, $W^{(o)}\ge0$ and $W^{(p)}>0$ their wealths, and $\gamma\ge0$ the lending yield per unit of volatility, with $\theta^{(o)}_1+\gamma>0$ (condition (11)). Let
--   $$R(y)=y\,(\theta^{(o)}_1+y)^-W^{(o)}+y\,(\theta^{(p)}_1+y)^-W^{(p)}$$
--   be the lending agent's revenue (10) and $M=\operatorname{argmax}_{y\ge\gamma}R(y)$ the set of $y\ge\gamma$ with $R(z)\le R(y)$ for all $z\ge\gamma$. Then
--
--   1. $M=[\gamma,\infty)$ if $\theta^{(p)}_1+\gamma\ge0$, and $M=\{\max\{\gamma,-\tfrac12\theta^{(p)}_1\}\}$ otherwise;
--   2. the least element of $M$ is
--   $$\phi=\max\Big\{\gamma,-\tfrac12\theta^{(p)}_1\Big\}.$$
--
--   Part 1 is (12): the optimist never shorts at a cost $y\ge\gamma$, so the revenue is the pessimist's alone; where she does not short at any admissible cost, the cost is undetermined. Part 2 is the selection (13) the paper makes from then on.
--
--   **Formalization Note** The page prints the undetermined case of (12) with the indicator $\mathbb 1_{\{\theta^{(p)}_1\ge0\}}$. The correct condition is $\theta^{(p)}_1+\gamma\ge0$ (that is, $\theta^{(p)}_2\ge0$ by (7)): for $\gamma=1$ and $\theta^{(p)}_1=-\tfrac12$ the revenue vanishes on $[1,\infty)$, so every $y\ge1$ is a maximizer while the printed formula gives $\{1\}$. The least element (13) is the same in every case. The hypothesis $\gamma\ge0$ holds in equilibrium by (14), and $\theta^{(o)}_1+\gamma>0$ is (11).
-- source:
--   Evgeniou, Hugonnier & Prieto, Asset Pricing with Costly Short Sales, SFI Research Paper N°22-21 (version of September 22, 2022), p. 18, (12)–(13)

import Mathlib
import Definitions.Def_CostlyShort_ShortMarket_Setting

namespace CostlyShort.ShortMarket

theorem eq12_eq13_cost_selection (θ₁o θ₁p Wo Wp γ : ℝ)
    (hγ : 0 ≤ γ) (hWo : 0 ≤ Wo) (hWp : 0 < Wp) (h11 : 0 < θ₁o + γ) :
    {y | γ ≤ y ∧ ∀ z, γ ≤ z → lendingRevenue θ₁o θ₁p Wo Wp z ≤ lendingRevenue θ₁o θ₁p Wo Wp y} =
        (if 0 ≤ θ₁p + γ then Set.Ici γ else {max γ (-θ₁p / 2)}) ∧
      IsLeast {y | γ ≤ y ∧ ∀ z, γ ≤ z →
        lendingRevenue θ₁o θ₁p Wo Wp z ≤ lendingRevenue θ₁o θ₁p Wo Wp y} (max γ (-θ₁p / 2)) := by sorry

end CostlyShort.ShortMarket
