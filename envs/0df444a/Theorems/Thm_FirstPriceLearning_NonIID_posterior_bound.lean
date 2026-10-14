-- Prove2me | Theorems.Thm_FirstPriceLearning_NonIID_posterior_bound
-- name    : FirstPriceLearning.NonIID.posterior_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:35.210778+00:00
-- url     : https://prove2.me/theorems/dc03932a-f44c-4ae4-a962-2bac8e8d5096
-- title:
--   Proof of Theorem 8, p. 34 — $\mathbb E_{m\sim\mathrm{Unif}\{0,1/8\}}[(v-b)\mathbb 1(b\ge m)]\le\max\{v/2,v-1/8\}=v-1/8$
-- statement:
--   Let $v\ge\frac14$ be a value and $b\in[0,1]$ a bid, and let $m$ be uniform on the two points $\{0,\frac18\}$. Then
--   $$
--   \mathbb E_{m\sim\mathrm{Uniform}(\{0,1/8\})}\big[(v-b)\mathbb 1(b\ge m)\big]\le\max_{b'\in[0,1]}\frac{v-b'}{2}\Big(1+\mathbb 1\big(b'\ge\tfrac18\big)\Big)=\max\Big\{\frac v2,\,v-\frac18\Big\}=v-\frac18 .
--   $$
--
--   In the proof of Theorem 8 the HOB $m_t$ is, given everything the bidder has observed, uniform on $\{0,1/8\}$; this inequality then caps the bidder's expected reward at every round by $v_t-1/8$, whatever she bids.
--
--   **Formalization Note** The uniform law is the measure $\tfrac12(\delta_0+\delta_{1/8})$ and the expectation its integral; $\max_{b'\in[0,1]}$ is a supremum over $[0,1]$. All three relations of the display are stated.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 34, proof of Theorem 8, posterior-reward display

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Auction

namespace FirstPriceLearning.NonIID

open MeasureTheory

/-- Proof of Theorem 8, arXiv:2003.09795v7, p. 34 (the posterior-reward display): for a value
`v ≥ 1/4` and a bid `b ∈ [0, 1]`, with `m` uniform on `{0, 1/8}`,
`E_m[(v − b) 𝟙(b ≥ m)] ≤ max_{b' ∈ [0,1]} ((v − b')/2)(1 + 𝟙(b' ≥ 1/8)) = max{v/2, v − 1/8} = v − 1/8`. -/
theorem posterior_bound (v b : ℝ) (hv : 1 / 4 ≤ v) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    ∫ m, FirstPriceLearning.Stochastic.payoff v b m ∂((2 : ENNReal)⁻¹ • (Measure.dirac (0 : ℝ) + Measure.dirac (1 / 8 : ℝ))) ≤
        ⨆ b' : Set.Icc (0 : ℝ) 1,
          (v - (b' : ℝ)) / 2 * (1 + (if (1 / 8 : ℝ) ≤ (b' : ℝ) then 1 else 0)) ∧
      (⨆ b' : Set.Icc (0 : ℝ) 1,
          (v - (b' : ℝ)) / 2 * (1 + (if (1 / 8 : ℝ) ≤ (b' : ℝ) then 1 else 0))) =
        max (v / 2) (v - 1 / 8) ∧
      max (v / 2) (v - 1 / 8) = v - 1 / 8 := by sorry

end FirstPriceLearning.NonIID
