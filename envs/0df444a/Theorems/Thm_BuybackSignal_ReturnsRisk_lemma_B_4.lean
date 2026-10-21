-- Prove2me | Theorems.Thm_BuybackSignal_ReturnsRisk_lemma_B_4
-- name    : BuybackSignal.ReturnsRisk.lemma_B_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:49.242559+00:00
-- url     : https://prove2.me/theorems/c49543f2-29a7-454e-b23f-22148f5941b2
-- title:
--   Lemma B.4, EC p. 9 — interior bounds on the transformed optimizer
-- statement:
--   Let $(\tilde w^\star,\tilde u^\star)$ minimize $\lambda\tilde w^2+\lambda^c\tilde u^2$ over the constraints (B.4), (B.6), and (B.7). Every such solution satisfies
--   $$
--   \tilde w^\star>-\frac{\alpha}{2\beta},\qquad
--   -\frac{\lambda\Delta\alpha}{2\beta}<\tilde u^\star<
--   \frac{\lambda\Delta\alpha}{2\beta}.
--   $$
--   These bounds locate the transformed optimum away from the stated boundaries.
-- source:
--   Wang, Gurnani & Subramanian, The Informational Role of Buyback Contracts, SSRN 3166462 (author's revised version; Management Science 2020), EC p. 9 (PDF 41), Lemma B.4

import Mathlib
import Definitions.Def_BuybackSignal_ReturnsRisk_Model

namespace BuybackSignal.ReturnsRisk

theorem lemma_B_4 (P : Params) (hP : P.Standing) (z : ℝ × ℝ)
    (hz : P.IsTransformedSolution z) :
    -P.alpha / (2 * P.β) < z.1 ∧
    -P.lam * P.dAlpha / (2 * P.β) < z.2 ∧
    z.2 < P.lam * P.dAlpha / (2 * P.β) := by sorry
end BuybackSignal.ReturnsRisk
