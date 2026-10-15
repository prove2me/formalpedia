-- Prove2me | Theorems.Thm_FirstPriceLearning_LowerBound_eq_20
-- name    : FirstPriceLearning.LowerBound.eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:34.712016+00:00
-- url     : https://prove2.me/theorems/59d9b05e-466f-49c3-89d8-8725867fb9e2
-- title:
--   (20), p. 37 — separation: under $G_1$ and $G_2$ every bid has summed instantaneous regret $\ge 2\Delta/3$
-- statement:
--   Let $\Delta\in(0,1/4)$, let $G_1,G_2$ be the two HOB laws of the two-point construction, let $v_t=1$, and write $R_i(v_t,b)=(1-b)G_i(b)$. Then for every bid $b_t\in[0,1]$,
--
--   $$
--   \Bigl(\max_{b\in[0,1]}R_1(v_t,b)-R_1(v_t,b_t)\Bigr)+\Bigl(\max_{b\in[0,1]}R_2(v_t,b)-R_2(v_t,b_t)\Bigr)
--   \ \ge\ \max_{b\in[0,1]}R_1(v_t,b)+\max_{b\in[0,1]}R_2(v_t,b)-\max_{b\in[0,1]}\bigl(R_1(v_t,b)+R_2(v_t,b)\bigr),
--   $$
--
--   and the right-hand side equals $2\Delta/3$.
--
--   This is the separation condition of Le Cam's two-point method: no single bid has small instantaneous regret under both $G_1$ and $G_2$.
--
--   **Formalization Note** The maxima are the oracle values of the model (suprema over $b\in[0,1]$, which are attained). The statement keeps both steps of the printed chain: the inequality for every $b_t\in[0,1]$ and the identity of its right-hand side with $2\Delta/3$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 37, App. B, (20)

import Mathlib
import Definitions.Def_FirstPriceLearning_LowerBound_Model
import Definitions.Def_FirstPriceLearning_LowerBound_TwoPointLaws

open MeasureTheory

namespace FirstPriceLearning.LowerBound

/-- arXiv:2003.09795v7, App. B, (20), p. 37 (separation condition): with `v_t = 1` and `Δ ∈ (0, 1/4)`,
for every bid `b_t ∈ [0, 1]` the two instantaneous regrets under `G₁` and `G₂` sum to at least
`max R₁ + max R₂ − max (R₁ + R₂)`, and this quantity equals `2Δ/3`. -/
theorem eq_20 (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) :
    (∀ bt ∈ Set.Icc (0 : ℝ) 1,
      FirstPriceLearning.Stochastic.oracle (lawG1 Δ) 1 + FirstPriceLearning.Stochastic.oracle (lawG2 Δ) 1
          - (⨆ b : Set.Icc (0 : ℝ) 1, (FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b + FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b)) ≤
        (FirstPriceLearning.Stochastic.oracle (lawG1 Δ) 1 - FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 bt)
          + (FirstPriceLearning.Stochastic.oracle (lawG2 Δ) 1 - FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 bt)) ∧
    FirstPriceLearning.Stochastic.oracle (lawG1 Δ) 1 + FirstPriceLearning.Stochastic.oracle (lawG2 Δ) 1
        - (⨆ b : Set.Icc (0 : ℝ) 1, (FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b + FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b)) =
      2 * Δ / 3 := by sorry

end FirstPriceLearning.LowerBound
