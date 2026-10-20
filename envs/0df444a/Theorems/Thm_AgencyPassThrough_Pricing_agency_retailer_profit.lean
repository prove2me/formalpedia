-- Prove2me | Theorems.Thm_AgencyPassThrough_Pricing_agency_retailer_profit
-- name    : AgencyPassThrough.Pricing.agency_retailer_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:43.448159+00:00
-- url     : https://prove2.me/theorems/da3127bc-4a80-419e-b472-3c57c58bba1f
-- title:
--   Proof of Proposition 2(i) — agency e-tailer profit formula and bound
-- statement:
--   At an agency equilibrium $p^B$, with $n$ suppliers, $c_s\geq0$, and $\theta^B\geq0$, the e-tailer's contract profit satisfies
--
--   $$\pi_r^B=n\lambda(p^B)q(p^B)\left[1+\frac{c_s\theta^B(\lambda(p^B)-p^B\lambda'(p^B))}{(p^B-\theta^B\lambda(p^B))^2}\right]\geq n\lambda(p^B)q(p^B).$$
--
--   This supplies the lower bound for the e-tailer's agency profit in Proposition 2(i). The profit itself is defined from the commission contract objective, independently of this reduced formula.
--
--   **Formalization Note** A4 supplies the nonnegative bracket correction, and the agency equilibrium predicate guards its denominator.
-- source:
--   Hu, Zheng & Pan, Agency or Wholesale? The Role of Retail Pass-Through, SSRN preprint 3724934 (2021 revision, PDF sha256 1ab91ed8…), p. 27, proof of Proposition 2(i), e-tailer profit

import Mathlib
import Definitions.Def_AgencyPassThrough_Pricing_Model

namespace AgencyPassThrough.Pricing

/-- Agency e-tailer profit identity and bound, proof of Proposition 2(i), p. 27. -/
theorem agency_retailer_profit (q : ℝ → ℝ) (D : Set ℝ)
    (hq : DemandStanding q D) (n : ℕ) (cs θB pB : ℝ)
    (hcs : 0 ≤ cs) (hθB0 : 0 ≤ θB)
    (hB : IsAgencyEq q D cs θB pB) :
    piBr n q cs θB pB = (n : ℝ) * lam q pB * q pB *
      (1 + cs * θB * (lam q pB - pB * deriv (lam q) pB) /
        (pB - θB * lam q pB) ^ 2) ∧
    (n : ℝ) * lam q pB * q pB ≤ piBr n q cs θB pB := by sorry

end AgencyPassThrough.Pricing
