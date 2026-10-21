-- Prove2me | Theorems.Thm_BuybackSignal_ReturnsRisk_lemma_B_6
-- name    : BuybackSignal.ReturnsRisk.lemma_B_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:43.902976+00:00
-- url     : https://prove2.me/theorems/b6a5f796-08b2-4b45-9499-a902128697cc
-- title:
--   Lemma B.6, EC p. 10 — equations and signs of the transformed optimizer
-- statement:
--   Every solution $(\tilde w^\star,\tilde u^\star)$ of the transformed problem (B.5)–(B.7) satisfies equations (B.27) and (B.28), and
--   $$
--   \tilde w^\star<0,\quad \tilde u^\star>0,\quad
--   0<\lambda\tilde w^\star+\lambda^c\tilde u^\star<
--   \lambda^c\tilde u^\dagger,\quad
--   \tilde w^\star-\tilde u^\star<-\tilde u^\dagger.
--   $$
--   Here $\tilde u^\dagger$ is the positive root in (B.24). These conditions supply the price and order comparisons in Proposition 1. They are necessary conditions for every optimizer; uniqueness of the equation system is not assumed.
-- source:
--   Wang, Gurnani & Subramanian, The Informational Role of Buyback Contracts, SSRN 3166462 (author's revised version; Management Science 2020), EC p. 10 (PDF 42), Lemma B.6, (B.27)–(B.28); EC p. 8 (PDF 40), (B.24)

import Mathlib
import Definitions.Def_BuybackSignal_ReturnsRisk_Model

namespace BuybackSignal.ReturnsRisk

theorem lemma_B_6 (P : Params) (hP : P.Standing) (z : ℝ × ℝ)
    (hz : P.IsTransformedSolution z) :
    P.b6 z.1 z.2 = 0 ∧
    P.lamC * z.2 ^ 2 - P.lam * z.1 ^ 2 +
      2 * P.lam * z.1 * z.2 -
      (P.lamC * P.lam * P.dAlpha / (2 * P.β)) * z.2 -
      (P.lam * P.alpha / (2 * P.β)) * z.1 = 0 ∧
    z.1 < 0 ∧ 0 < z.2 ∧
    0 < P.lam * z.1 + P.lamC * z.2 ∧
    P.lam * z.1 + P.lamC * z.2 < P.lamC * P.uDag ∧
    z.1 - z.2 < -P.uDag := by sorry
end BuybackSignal.ReturnsRisk
