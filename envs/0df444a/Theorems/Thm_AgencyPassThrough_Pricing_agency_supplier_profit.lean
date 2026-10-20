-- Prove2me | Theorems.Thm_AgencyPassThrough_Pricing_agency_supplier_profit
-- name    : AgencyPassThrough.Pricing.agency_supplier_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:37.251191+00:00
-- url     : https://prove2.me/theorems/3e98f766-cf1f-41c8-b66d-e3c4b4292e7b
-- title:
--   Proof of Proposition 2(i) — agency supplier profit formula and bound
-- statement:
--   At an agency equilibrium $p^B$, with $c_s\geq0$ and $\theta^B\geq0$, each supplier's contract profit has the form
--
--   $$\pi_i^B=\frac{c_s\theta^B\lambda(p^B)q(p^B)}{p^B-\theta^B\lambda(p^B)}\leq\dot\pi(p^B).$$
--
--   This is the supplier-profit comparison used in Proposition 2(i). The contract profit is defined from commission revenue minus production cost, independently of this reduced formula.
--
--   **Formalization Note** The agency equilibrium predicate ensures the denominator is positive.
-- source:
--   Hu, Zheng & Pan, Agency or Wholesale? The Role of Retail Pass-Through, SSRN preprint 3724934 (2021 revision, PDF sha256 1ab91ed8…), p. 27, proof of Proposition 2(i), agency supplier profit

import Mathlib
import Definitions.Def_AgencyPassThrough_Pricing_Model

namespace AgencyPassThrough.Pricing

/-- Agency supplier profit and its comparison with π̇, proof of Proposition 2(i), p. 27. -/
theorem agency_supplier_profit (q : ℝ → ℝ) (D : Set ℝ)
    (hq : DemandStanding q D) (cs θB pB : ℝ) (hcs : 0 ≤ cs)
    (hθB0 : 0 ≤ θB) (hB : IsAgencyEq q D cs θB pB) :
    piBi q cs θB pB = cs * θB * lam q pB * q pB /
      (pB - θB * lam q pB) ∧
    piBi q cs θB pB ≤ piDot q cs pB := by sorry

end AgencyPassThrough.Pricing
