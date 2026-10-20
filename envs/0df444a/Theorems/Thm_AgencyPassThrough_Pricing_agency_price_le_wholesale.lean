-- Prove2me | Theorems.Thm_AgencyPassThrough_Pricing_agency_price_le_wholesale
-- name    : AgencyPassThrough.Pricing.agency_price_le_wholesale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:18.48515+00:00
-- url     : https://prove2.me/theorems/b8647388-9c58-4c30-9431-dfc3e8f1da2f
-- title:
--   Proof of Proposition 2(i) — agency retail price does not exceed wholesale
-- statement:
--   Consider any wholesale and agency equilibrium prices $p^W,p^B$ in the price domain, with supplier unit cost $c_s\geq0$. If the conduct parameters obey $0\leq\theta^B\leq\theta^W\leq1$, then
--
--   $$p^B\leq p^W.$$
--
--   This is the price conclusion in Proposition 2(i), stated for generic conduct parameters so it can be reused after Proposition 1 connects them to pass-through.
--
--   **Formalization Note** An equilibrium price means a solution of its respective Lemma 1 equation; existence or uniqueness is not asserted.
-- source:
--   Hu, Zheng & Pan, Agency or Wholesale? The Role of Retail Pass-Through, SSRN preprint 3724934 (2021 revision, PDF sha256 1ab91ed8…), p. 26, proof of Proposition 2(i), pp. 26–27

import Mathlib
import Definitions.Def_AgencyPassThrough_Pricing_Model

namespace AgencyPassThrough.Pricing

/-- First conclusion of Proposition 2(i), proved in Appendix B, pp. 26–27. -/
theorem agency_price_le_wholesale (q : ℝ → ℝ) (D : Set ℝ)
    (hq : DemandStanding q D) (cs θW θB pW pB : ℝ)
    (hcs : 0 ≤ cs) (hθB0 : 0 ≤ θB) (hθBW : θB ≤ θW) (hθW1 : θW ≤ 1)
    (hW : IsWholesaleEq q D cs θW pW) (hB : IsAgencyEq q D cs θB pB) :
    pB ≤ pW := by sorry

end AgencyPassThrough.Pricing
