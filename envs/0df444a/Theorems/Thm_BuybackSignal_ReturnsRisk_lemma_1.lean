-- Prove2me | Theorems.Thm_BuybackSignal_ReturnsRisk_lemma_1
-- name    : BuybackSignal.ReturnsRisk.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:42.944904+00:00
-- url     : https://prove2.me/theorems/af27be48-1fed-4638-b887-ca422239ee07
-- title:
--   Lemma 1, p. 10 (PDF 10) — the retailer’s optimal order (1) and realized unsold stock at optimal retail prices
-- statement:
--   Let $\hat\lambda\in(0,1)$, $\hat\theta\in[\underline\theta,\bar\theta]$, and $w,r\ge0$. Write $\Pi^R_i(s\mid w,r,\hat\theta)=\max_{0\le p\le\alpha_i/\beta}\,p\min\{d_i,s\}+\hat\theta r\,[s-\min\{d_i,s\}]-ws$ with $d_i=\alpha_i-\beta p$ for the retailer's posterior profit (A.1). If $w-\hat\theta r\ge0$ and the order $s^R$ in (1) is nonnegative, then $s^R$ maximizes the retailer's ex ante profit (A.4) over all $s\ge0$:
--   $$
--   \hat\lambda\,\Pi^R_h(s)+\hat\lambda^c\,\Pi^R_l(s)\le
--   \hat\lambda\,\Pi^R_h(s^R)+\hat\lambda^c\,\Pi^R_l(s^R)\qquad(s\ge0).
--   $$
--   With stock $s^R$, an optimal retail price exists after each baseline realization. Every optimal price after high baseline demand $\alpha_h$ leaves no stock unsold, $s^R-\min\{d_h,s^R\}=0$. If moreover $\beta\hat\theta r\le\alpha_l$, every optimal price after low baseline demand $\alpha_l$ leaves exactly
--   $$
--   s^R-\min\{d_l,s^R\}=\tfrac12\left[\Delta\alpha-(\beta/\hat\lambda)(w-\hat\theta r)\right]^+
--   $$
--   units unsold.
--
--   This ties the order formula (1) and the unsold quantities that enter the manufacturer's profit (2) to the retailer's actual stock and price optimization.
--
--   **Formalization Note** Two hypotheses are added. The printed formula (1) is negative for a large wholesale price, while orders are nonnegative, so $s^R\ge0$ is assumed. The low-demand leftover is claimed only when $\beta\hat\theta r\le\alpha_l$, the price cap of Lemma A.1 (the optimal clearance price $(\alpha_l+\beta\hat\theta r)/(2\beta)$ must not exceed $\alpha_l/\beta$). Without it the printed amount can exceed the stock: at $(\alpha_h,\alpha_l,\beta,\lambda)=(10,4,1,\tfrac12)$, $w=r=9$, $\hat\theta=1$, the order is $\tfrac12$ and the formula gives $3$. The optimality and high-demand claims need no such cap. "Unsold" is the realized leftover $s-\min\{d_i,s\}$ at an optimal price of (A.1), not a formula.
-- source:
--   Wang, Gurnani & Subramanian, The Informational Role of Buyback Contracts, SSRN 3166462 (author's revised version; Management Science 2020), p. 10 (PDF 10), Lemma 1 and (1); EC pp. 1–2 (PDF 33–34), proof

import Mathlib
import Definitions.Def_BuybackSignal_ReturnsRisk_Model

namespace BuybackSignal.ReturnsRisk

theorem lemma_1 (P : Params) (hP : P.Standing)
    (w r θhat probHat : ℝ) (hprob : 0 < probHat ∧ probHat < 1)
    (hw : 0 ≤ w) (hr : 0 ≤ r) (hθ : P.θlow ≤ θhat ∧ θhat ≤ P.θbar)
    (hcost : 0 ≤ w - θhat * r) (horder : 0 ≤ P.sR w r θhat probHat) :
    (∀ s : ℝ, 0 ≤ s →
      P.exAnteProfit s w r θhat probHat ≤
        P.exAnteProfit (P.sR w r θhat probHat) w r θhat probHat) ∧
    (∃ p, P.IsOptimalPrice P.αh (P.sR w r θhat probHat) w r θhat p) ∧
    (∀ p, P.IsOptimalPrice P.αh (P.sR w r θhat probHat) w r θhat p →
      P.leftover P.αh (P.sR w r θhat probHat) p = 0) ∧
    (P.β * θhat * r ≤ P.αl →
      (∃ p, P.IsOptimalPrice P.αl (P.sR w r θhat probHat) w r θhat p) ∧
      ∀ p, P.IsOptimalPrice P.αl (P.sR w r θhat probHat) w r θhat p →
        P.leftover P.αl (P.sR w r θhat probHat) p =
          P.unsoldLow w r θhat probHat) := by sorry
end BuybackSignal.ReturnsRisk
