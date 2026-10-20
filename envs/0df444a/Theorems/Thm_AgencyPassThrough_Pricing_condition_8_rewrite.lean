-- Prove2me | Theorems.Thm_AgencyPassThrough_Pricing_condition_8_rewrite
-- name    : AgencyPassThrough.Pricing.condition_8_rewrite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:40.07482+00:00
-- url     : https://prove2.me/theorems/7188a1bd-7fb7-4e58-a709-bd30e0eeff89
-- title:
--   Proof of Proposition 2(ii) — condition (8) in terms of K^B
-- statement:
--   At an agency equilibrium $p^B$, for any proposed wholesale conduct parameter $\theta^W$, the price-side condition (8) is equivalent to the threshold comparison
--
--   $$\lambda(p^B)+\theta^W\lambda(p^B)[1-\lambda'(p^B)]<p^B-c_s\quad\Longleftrightarrow\quad\theta^W<\theta^B K^B.$$
--
--   The threshold is positive when $c_s>0$. This is the algebraic step behind the negative cross-brand pass-through case of Proposition 2.
--
--   **Formalization Note** If $c_s=0$, then $\alpha^B=K^B=0$, so strict positivity of $K^B$ is asserted only for positive supplier cost.
-- source:
--   Hu, Zheng & Pan, Agency or Wholesale? The Role of Retail Pass-Through, SSRN preprint 3724934 (2021 revision, PDF sha256 1ab91ed8…), p. 27, proof of Proposition 2(ii), Eq. (8) rewrite

import Mathlib
import Definitions.Def_AgencyPassThrough_Pricing_Model

namespace AgencyPassThrough.Pricing

/-- Rewriting condition (8) with K^B, proof of Proposition 2(ii), p. 27. -/
theorem condition_8_rewrite (q : ℝ → ℝ) (D : Set ℝ)
    (hq : DemandStanding q D) (cs θW θB pB : ℝ)
    (hcs : 0 ≤ cs) (hθB0 : 0 ≤ θB)
    (hB : IsAgencyEq q D cs θB pB) :
    (lam q pB + θW * lam q pB * (1 - deriv (lam q) pB) < pB - cs ↔
      θW < θB * KB q cs θB pB) ∧
    (0 < cs → 0 < KB q cs θB pB) := by sorry

end AgencyPassThrough.Pricing
