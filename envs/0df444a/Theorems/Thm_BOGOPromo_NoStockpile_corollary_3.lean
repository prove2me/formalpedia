-- Prove2me | Theorems.Thm_BOGOPromo_NoStockpile_corollary_3
-- name    : BOGOPromo.NoStockpile.corollary_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:34.80099+00:00
-- url     : https://prove2.me/theorems/36e96854-60aa-4be2-85eb-fe1c10f62c24
-- title:
--   Corollary 3, p. 22 (PDF 22) — at any w the retailer prefers BOGO (or NP) to PR; the BOGO–PR profit gap decreases in θ
-- statement:
--   Let $0<\theta\le 1$ and $0<w\le 1$.
--
--   1. The profit of any best response of the retailer in the PR game is at most the profit of any best response in the BOGO game:
--   $$\pi^*_{dr}(w;\theta)\le\pi^*_{br}(w;\theta).$$
--   Hence, with all three regimes available, a BOGO or a single price is always optimal.
--   2. On the region where price reduction beats no promotion, i.e. $1/3<\theta$ and $0<w\le\bar\theta$, the difference $\pi^*_{br}(w;\theta)-\pi^*_{dr}(w;\theta)$ is strictly decreasing in $\theta$: for $1/3<\theta_1<\theta_2\le 1$ with $w\le\bar\theta(\theta_1)$ and $w\le\bar\theta(\theta_2)$,
--   $$\pi^*_{br}(w;\theta_2)-\pi^*_{dr}(w;\theta_2)<\pi^*_{br}(w;\theta_1)-\pi^*_{dr}(w;\theta_1).$$
--
--   **Formalization Note** The monotonicity is stated on the PR region only. Outside it the PR game's best response is the single price, and the difference becomes the BOGO-versus-no-promotion gap, which increases in $\theta$; the text before the corollary restricts the comparison to "the regions where they are both preferable to no promotion" (p. 22).
-- source:
--   Li, Khouja, Pan & Zhou, Buy-One-Get-One Promotions in a Two-Echelon Supply Chain, SSRN working paper 3561162, p. 22 (PDF 22), Corollary 3

import Mathlib
import Definitions.Def_BOGOPromo_NoStockpile_Model

namespace BOGOPromo.NoStockpile

theorem corollary_3 :
    (∀ θ w : ℝ, 0 < θ → θ ≤ 1 → 0 < w → w ≤ 1 →
      ∀ πd : PPolicy, ∀ πb : BPolicy, IsBestRespP θ w πd → IsBestRespB θ w πb →
        πd.profit θ w ≤ πb.profit θ w) ∧
    (∀ θ₁ θ₂ w : ℝ, 1 / 3 < θ₁ → θ₁ < θ₂ → θ₂ ≤ 1 → 0 < w → w ≤ thetaBar θ₁ → w ≤ thetaBar θ₂ →
      ∀ (πb₁ πb₂ : BPolicy) (πd₁ πd₂ : PPolicy),
        IsBestRespB θ₁ w πb₁ → IsBestRespP θ₁ w πd₁ →
        IsBestRespB θ₂ w πb₂ → IsBestRespP θ₂ w πd₂ →
        πb₂.profit θ₂ w - πd₂.profit θ₂ w < πb₁.profit θ₁ w - πd₁.profit θ₁ w) := by sorry

end BOGOPromo.NoStockpile
