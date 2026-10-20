-- Prove2me | Theorems.Thm_AgencyPassThrough_Pricing_piDot_monotone
-- name    : AgencyPassThrough.Pricing.piDot_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:21.220956+00:00
-- url     : https://prove2.me/theorems/7aaca3cc-c50a-44da-9423-3f92e51c1efe
-- title:
--   Proof of Proposition 2(i) — auxiliary supplier profit up to wholesale price
-- statement:
--   Write $\dot\pi(p)=[p-c_s-\lambda(p)]q(p)$. At a wholesale equilibrium $p^W$ with $0\leq\theta^W\leq1$, every $p\in D$ with $p\leq p^W$ satisfies
--
--   $$\dot\pi(p)\leq\dot\pi(p^W)=\pi_i^W.$$
--
--   This compares the agency price's auxiliary profit to each supplier's wholesale profit after the price ordering is known.
--
--   **Formalization Note** The comparison ranges over the price domain and prices no greater than $p^W$; it does not assume an optimizer of $\dot\pi$ exists.
-- source:
--   Hu, Zheng & Pan, Agency or Wholesale? The Role of Retail Pass-Through, SSRN preprint 3724934 (2021 revision, PDF sha256 1ab91ed8…), p. 27, proof of Proposition 2(i), auxiliary profit comparison

import Mathlib
import Definitions.Def_AgencyPassThrough_Pricing_Model

namespace AgencyPassThrough.Pricing

/-- The π̇ comparison and wholesale supplier profit identity, proof of Proposition 2(i), p. 27. -/
theorem piDot_monotone (q : ℝ → ℝ) (D : Set ℝ) (hq : DemandStanding q D)
    (cs θW pW : ℝ) (hθW0 : 0 ≤ θW) (hθW1 : θW ≤ 1)
    (hW : IsWholesaleEq q D cs θW pW) :
    (∀ p ∈ D, p ≤ pW → piDot q cs p ≤ piDot q cs pW) ∧
      piDot q cs pW = piWi q cs pW := by sorry

end AgencyPassThrough.Pricing
