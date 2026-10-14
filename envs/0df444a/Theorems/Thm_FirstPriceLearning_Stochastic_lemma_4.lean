-- Prove2me | Theorems.Thm_FirstPriceLearning_Stochastic_lemma_4
-- name    : FirstPriceLearning.Stochastic.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:53.303189+00:00
-- url     : https://prove2.me/theorems/df82ed3d-7372-4eec-8b9d-e46cb9b96470
-- title:
--   Lemma 4, p. 20 — quantization costs at most (2/M + 1/K)T regret
-- statement:
--   Let $M,K\ge1$, let $G$ be any CDF on $[0,1]$, let $v=(v_1,\dots,v_T)\in[0,1]^T$ be an arbitrary value sequence and $\tilde v_t=\min\{x\in\mathcal C:x\ge v_t\}$ its clipping to $\mathcal C=\{1/M,\dots,1\}$. Let $b_1,\dots,b_T$ be bids on the grid $\mathcal A=\{1/K,\dots,1\}$: the bids of a policy $\pi^{\mathrm Q}$ of the quantized problem, which the induced policy $\pi$ plays in the original problem. Then
--
--   $$
--   R_T(\pi,v)\ \le\ \tilde R_T(\pi^{\mathrm Q},v)+\Big(\frac2M+\frac1K\Big)T,\qquad \tilde R_T(\pi^{\mathrm Q},v)=\sum_{t=1}^T\Big(\max_{b\in\mathcal A}R(\tilde v_t,b)-R(\tilde v_t,b_t)\Big),
--   $$
--
--   where $R_T(\pi,v)$ is the regret (3), computed with the maximum over all bids in $[0,1]$ and the true values.
--
--   This is the step that transfers a regret bound for the finite contextual bandit to the continuous auction.
--
--   **Formalization Note.** The statement is pathwise: it holds for every bid sequence on the grid, so it applies to every realization of a randomized $\pi^{\mathrm Q}$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 20, Lemma 4

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Auction

namespace FirstPriceLearning.Stochastic

open MeasureTheory

/-- Lemma 4 (p. 20): quantization loses at most `(2/M + 1/K) T`. For any value sequence
`v ∈ [0,1]^T`, any HOB law `G` on `[0, 1]` and any bids `b_t` on the grid `𝒜 = {1/K, …, 1}` (the
bids of a policy `π^Q` of the quantized problem, which the induced policy `π` also plays), the
regret (3) is at most the quantized regret `R̃_T(π^Q, v)`, computed against the clipped values
`ṽ_t = min {x ∈ 𝒞 : x ≥ v_t}`, `𝒞 = {1/M, …, 1}`, plus `(2/M + 1/K) T`. -/
theorem lemma_4 (T M K : ℕ) (hM : 1 ≤ M) (hK : 1 ≤ K) (μG : Measure ℝ) [IsProbabilityMeasure μG]
    (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (b : Fin T → ℝ) (hb : ∀ t, b t ∈ gridA K) :
    regret μG v b ≤
      gridRegret μG (gridA K) (fun t => clipValue M (v t)) b + (2 / M + 1 / K) * T := by sorry

end FirstPriceLearning.Stochastic
