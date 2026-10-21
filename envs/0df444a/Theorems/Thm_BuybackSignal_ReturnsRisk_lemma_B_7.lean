-- Prove2me | Theorems.Thm_BuybackSignal_ReturnsRisk_lemma_B_7
-- name    : BuybackSignal.ReturnsRisk.lemma_B_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:53.425895+00:00
-- url     : https://prove2.me/theorems/38a771d6-d225-4990-9f15-2c0674f33c2d
-- title:
--   Lemma B.7, EC p. 12 — no profitable off-path deviation by the less risky type
-- statement:
--   Let $(\bar w^\star,\bar r^\star)$ be any solution of problem (4). For every $(\bar w,\bar r)$ with $\bar w\ge\bar\theta\bar r\ge0$, the less risky manufacturer's profit when the retailer believes it is riskier obeys
--   $$
--   \Pi(\bar w,\bar r\mid\underline\theta,\bar\theta)
--   \le \Pi(\bar w^\star,\bar r^\star\mid\bar\theta,\bar\theta).
--   $$
--   This global bound is the less risky type's off-path no-deviation condition in Proposition 1.
-- source:
--   Wang, Gurnani & Subramanian, The Informational Role of Buyback Contracts, SSRN 3166462 (author's revised version; Management Science 2020), EC p. 12 (PDF 44), Lemma B.7

import Mathlib
import Definitions.Def_BuybackSignal_ReturnsRisk_Model

namespace BuybackSignal.ReturnsRisk

theorem lemma_B_7 (P : Params) (hP : P.Standing)
    (cstar : ℝ × ℝ) (hstar : P.IsSolution4 cstar) :
    ∀ c : ℝ × ℝ, c ∈ P.actionSet P.θbar →
      P.Pi c.1 c.2 P.θlow P.θbar ≤
        P.Pi cstar.1 cstar.2 P.θbar P.θbar := by sorry
end BuybackSignal.ReturnsRisk
