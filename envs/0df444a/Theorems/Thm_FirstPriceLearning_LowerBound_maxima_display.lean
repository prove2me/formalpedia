-- Prove2me | Theorems.Thm_FirstPriceLearning_LowerBound_maxima_display
-- name    : FirstPriceLearning.LowerBound.maxima_display
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:26.766057+00:00
-- url     : https://prove2.me/theorems/15ef6b3b-2fbe-4aa8-8652-258437610400
-- title:
--   App. B, p. 37 — the oracle rewards under $G_1$, $G_2$ and $G_1+G_2$: $(1+2\Delta)/3$, $1/3$, $2/3$
-- statement:
--   Let $\Delta\in(0,1/4)$, let $G_1,G_2$ be the two HOB laws of the two-point construction (masses $\tfrac12\pm\Delta$ at $1/3$ and $\tfrac12\mp\Delta$ at $2/3$), and let the value be $v_t=1$, so that $R_i(v_t,b)=(1-b)G_i(b)$. Then
--
--   $$
--   \max_{b\in[0,1]}(1-b)G_1(b)=\frac{1+2\Delta}{3},\qquad
--   \max_{b\in[0,1]}(1-b)G_2(b)=\frac13,\qquad
--   \max_{b\in[0,1]}(1-b)\bigl(G_1(b)+G_2(b)\bigr)=\frac23 ,
--   $$
--
--   and each maximum is attained on $[0,1]$.
--
--   These three values quantify the conflict between the two hypotheses: the best bid under $G_1$ is $1/3$, under $G_2$ it is $2/3$, and no single bid is optimal for both. They feed the separation condition (20).
--
--   **Formalization Note** Each maximum is stated as the greatest element of the image of $[0,1]$, which asserts both the value and its attainment.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 37, App. B, display before (20)

import Mathlib
import Definitions.Def_FirstPriceLearning_LowerBound_Model
import Definitions.Def_FirstPriceLearning_LowerBound_TwoPointLaws

open MeasureTheory

namespace FirstPriceLearning.LowerBound

/-- arXiv:2003.09795v7, App. B, p. 37, display before (20): with `v_t = 1` and `Δ ∈ (0, 1/4)`,
`max_{b∈[0,1]} (1 − b)G₁(b) = (1 + 2Δ)/3`, `max_{b∈[0,1]} (1 − b)G₂(b) = 1/3` and
`max_{b∈[0,1]} (1 − b)(G₁(b) + G₂(b)) = 2/3`, each maximum attained on `[0, 1]`. -/
theorem maxima_display (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) :
    IsGreatest ((fun b => FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b) '' Set.Icc (0 : ℝ) 1) ((1 + 2 * Δ) / 3) ∧
    IsGreatest ((fun b => FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b) '' Set.Icc (0 : ℝ) 1) (1 / 3) ∧
    IsGreatest ((fun b => FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b + FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b) '' Set.Icc (0 : ℝ) 1)
      (2 / 3) := by sorry

end FirstPriceLearning.LowerBound
