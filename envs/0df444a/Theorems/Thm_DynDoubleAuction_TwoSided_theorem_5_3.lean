-- Prove2me | Theorems.Thm_DynDoubleAuction_TwoSided_theorem_5_3
-- name    : DynDoubleAuction.TwoSided.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:55.372986+00:00
-- url     : https://prove2.me/theorems/a0fc4ed9-efcf-4407-8ec7-2b04286ed46a
-- title:
--   Theorem 5.3 — first-best profit asymptotics
-- statement:
--   Under Assumption 5.1, start every agent at $w^1=\underline w_0+\bar v\sqrt{8T\log T}$. Whenever $w^1\le\bar w^1-\bar v(1+\sqrt{8T\log T})$, there is a constant $C$ independent of $T$ such that for all integer $T\ge2$,
--
--   $$\Pi\ge\Pi^{\mathrm{FB}}-C\sqrt{T\log T}.$$
--
--   For the same market and mechanism, the profit ratio converges:
--
--   $$\frac{\Pi}{\Pi^{\mathrm{FB}}}\longrightarrow1\quad\text{as }T\longrightarrow\infty.$$
--
--   This is both parts of Theorem 5.3: a sublinear additive shortfall and asymptotic first-best profit.
--
--   **Formalization Note** The fixed constant may depend on the market distribution, reserve, weights, number of buyers, and value bound. The profit is the integral of the mechanism's transfer path, and the benchmark is $T\underline w_0$.
-- source:
--   Balseiro, Mirrokni, Paes Leme & Zuo, Dynamic Double Auctions: Towards First Best, SSRN 3213460 (version of November 15, 2018), p. 29, Theorem 5.3

import Mathlib
import Definitions.Def_DynDoubleAuction_TwoSided_Model

namespace DynDoubleAuction.TwoSided

open MeasureTheory Filter Topology

/-- Theorem 5.3: the coupled mechanism approaches the first-best profit. -/
theorem theorem_5_3 {n : ℕ} (M : Market n) (hM : Standing M) :
    (∃ C : ℝ, ∀ T : ℕ, 2 ≤ T →
      initialPromise M T ≤ wbar M T 1 -
        M.vbar * (1 + Real.sqrt (8 * (T : ℝ) * Real.log T)) →
      firstBest M T - C * Real.sqrt ((T : ℝ) * Real.log T) ≤
        expectedProfit M T (initialPromise M T)) ∧
    Tendsto (fun T : ℕ =>
      expectedProfit M T (initialPromise M T) / firstBest M T)
      atTop (𝓝 1) := by sorry
end DynDoubleAuction.TwoSided
