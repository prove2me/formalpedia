-- Prove2me | Theorems.Thm_BOGOPromo_NoStockpile_corollary_4
-- name    : BOGOPromo.NoStockpile.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:35.270563+00:00
-- url     : https://prove2.me/theorems/cae8cbe8-c9c8-4104-8d0a-667316a6bb5d
-- title:
--   Corollary 4, pp. 23–24 (PDF 23–24) — for c < c̄(θ): manufacturer indifferent; BOGO gives retailer and supply chain more profit and the retailer a larger share than PR or no promotion
-- statement:
--   Fix a unit production cost $c\ge 0$. For $0<\theta\le 1$ with $c<\bar c(\theta)$, take any equilibrium of the BOGO game, any equilibrium of the PR game and any equilibrium of the no-promotion game, each with the manufacturer leading. Write $\pi^*_{bm},\pi^*_{br}$ for the manufacturer's and retailer's profits in the BOGO equilibrium, $\pi^*_{dm},\pi^*_{dr}$ in the PR equilibrium and $\pi^*_{nm},\pi^*_{nr}$ in the no-promotion equilibrium. Then:
--
--   1. The manufacturer is indifferent between PR and BOGO: $\pi^*_{bm}=\pi^*_{dm}$.
--   2. The retailer offers a BOGO $(p^*_b,p^*_g)$ in the BOGO game and a price reduction $(p^*_r,p^*_d)$ in the PR game, with equal regular prices $p^*_b=p^*_r$, and for $\theta<1$ the BOGO price is lower, $p^*_g<p^*_d$.
--   3. The retailer and the supply chain earn more with BOGO than with no promotion,
--   $$\pi^*_{nr}<\pi^*_{br},\qquad \pi^*_{nm}+\pi^*_{nr}<\pi^*_{bm}+\pi^*_{br};$$
--   for $\theta<1$ they also earn more with BOGO than with PR, $\pi^*_{dr}<\pi^*_{br}$ and $\pi^*_{dm}+\pi^*_{dr}<\pi^*_{bm}+\pi^*_{br}$; at $\theta=1$ the retailer's BOGO and PR profits are equal.
--   4. For $\theta<1$ the retailer's share of supply-chain profit is largest under BOGO:
--   $$\frac{\pi^*_{dr}}{\pi^*_{dm}+\pi^*_{dr}}<\frac{\pi^*_{br}}{\pi^*_{bm}+\pi^*_{br}},\qquad \frac{\pi^*_{nr}}{\pi^*_{nm}+\pi^*_{nr}}<\frac{\pi^*_{br}}{\pi^*_{bm}+\pi^*_{br}}.$$
--
--   Moreover, for $0<\theta_1<\theta_2\le 1$ with $c<\bar c(\theta_1)$ and $c<\bar c(\theta_2)$, comparing any equilibria at $\theta_1$ and at $\theta_2$, the price gap $p^*_d-p^*_g$, the retailer's BOGO advantage $\pi^*_{br}-\pi^*_{dr}$ and the retailer's BOGO share $\pi^*_{br}/(\pi^*_{bm}+\pi^*_{br})$ are all strictly smaller at $\theta_2$ (decreasing in $\theta$).
--
--   This is the paper's headline comparison: without stockpiling, BOGO reallocates supply-chain profit toward the retailer while leaving the manufacturer's profit unchanged.
--
--   **Formalization Note** The page states "higher", "lower" and "larger" without exception, but the same corollary says the BOGO and PR profits are equal at $\theta=1$, where the prices and the shares are also equal (both shares are $1/3$, as is the no-promotion share). The strict BOGO-versus-PR claims and the share claims are therefore stated for $\theta<1$, with equality of the retailer's profits at $\theta=1$ as its own clause; the BOGO-versus-no-promotion profit claims are strict for every $\theta$ in the region. The hypothesis is $c<\bar c(\theta)$ as written; the parenthetical gloss "the region in which both BOGO and PR are more profitable than no promotion" is not used. "Decreasing in $\theta$" is strict decrease for fixed $c$ between any two values of $\theta$ in the region. The statement quantifies over all equilibria; it does not assume the closed forms of Table 3.
-- source:
--   Li, Khouja, Pan & Zhou, Buy-One-Get-One Promotions in a Two-Echelon Supply Chain, SSRN working paper 3561162, pp. 23–24 (PDF 23–24), Corollary 4

import Mathlib
import Definitions.Def_BOGOPromo_NoStockpile_Model

namespace BOGOPromo.NoStockpile

theorem corollary_4 (c : ℝ) (hc0 : 0 ≤ c) :
    (∀ θ : ℝ, 0 < θ → θ ≤ 1 → c < cBar θ →
      ∀ (wb : ℝ) (rb : ℝ → BPolicy) (wd : ℝ) (rd : ℝ → PPolicy) (wn : ℝ) (rn : ℝ → ℝ),
        IsEqB θ c wb rb → IsEqP θ c wd rd → IsEqN c wn rn →
        let πbm := (wb - c) * (rb wb).demand θ
        let πbr := (rb wb).profit θ wb
        let πdm := (wd - c) * (rd wd).demand θ
        let πdr := (rd wd).profit θ wd
        let πnm := (wn - c) * npDemand (rn wn)
        let πnr := npProfit wn (rn wn)
        -- part 1
        πbm = πdm ∧
        -- part 2
        (∃ pb pg pr pd : ℝ, rb wb = .bogo pb pg ∧ rd wd = .priceRed pr pd ∧ pb = pr ∧
          (θ < 1 → pg < pd)) ∧
        -- part 3
        πnr < πbr ∧ πnm + πnr < πbm + πbr ∧
        (θ < 1 → πdr < πbr ∧ πdm + πdr < πbm + πbr) ∧ (θ = 1 → πbr = πdr) ∧
        -- part 4
        (θ < 1 → πdr / (πdm + πdr) < πbr / (πbm + πbr) ∧
          πnr / (πnm + πnr) < πbr / (πbm + πbr))) ∧
    (∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ < θ₂ → θ₂ ≤ 1 → c < cBar θ₁ → c < cBar θ₂ →
      ∀ (wb₁ wd₁ wb₂ wd₂ : ℝ) (rb₁ rb₂ : ℝ → BPolicy) (rd₁ rd₂ : ℝ → PPolicy),
        IsEqB θ₁ c wb₁ rb₁ → IsEqP θ₁ c wd₁ rd₁ → IsEqB θ₂ c wb₂ rb₂ → IsEqP θ₂ c wd₂ rd₂ →
        -- part 2: the price gap p_d − p_g decreases in θ
        (rd₂ wd₂).promoPrice - (rb₂ wb₂).promoPrice <
          (rd₁ wd₁).promoPrice - (rb₁ wb₁).promoPrice ∧
        -- part 3: the retailer's BOGO advantage over PR decreases in θ
        (rb₂ wb₂).profit θ₂ wb₂ - (rd₂ wd₂).profit θ₂ wd₂ <
          (rb₁ wb₁).profit θ₁ wb₁ - (rd₁ wd₁).profit θ₁ wd₁ ∧
        -- part 4: the retailer's share of supply-chain profit under BOGO decreases in θ
        (rb₂ wb₂).profit θ₂ wb₂ / ((wb₂ - c) * (rb₂ wb₂).demand θ₂ + (rb₂ wb₂).profit θ₂ wb₂) <
          (rb₁ wb₁).profit θ₁ wb₁ / ((wb₁ - c) * (rb₁ wb₁).demand θ₁ + (rb₁ wb₁).profit θ₁ wb₁)) := by sorry

end BOGOPromo.NoStockpile
