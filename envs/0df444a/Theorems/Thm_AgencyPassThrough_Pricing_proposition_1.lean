-- Prove2me | Theorems.Thm_AgencyPassThrough_Pricing_proposition_1
-- name    : AgencyPassThrough.Pricing.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:18.493211+00:00
-- url     : https://prove2.me/theorems/aa2b627a-25ad-4094-ad29-143a3eab0ca6
-- title:
--   Proposition 1 — pass-through sign orders supplier conduct parameters
-- statement:
--   Let $n\geq2$, $0\leq\epsilon<1$, and $a-\epsilon b>0$. The wholesale and agency supplier conduct parameters satisfy
--
--   $$\theta^W-\theta^B=\frac{(1-\epsilon)(n-1+\epsilon)b}{a-\epsilon b}.$$
--
--   Thus $\theta^W<\theta^B$ exactly when the cross-brand pass-through $b$ is negative, and $\theta^W\geq\theta^B$ whenever $b\geq0$. This is the conduct-parameter comparison used in both cases of Proposition 2.
--
--   **Formalization Note** The strict bound $\epsilon<1$ follows from A1's strict total-demand decrease. The positive denominator is stated explicitly.
-- source:
--   Hu, Zheng & Pan, Agency or Wholesale? The Role of Retail Pass-Through, SSRN preprint 3724934 (2021 revision, PDF sha256 1ab91ed8…), p. 12, Proposition 1; proof p. 26

import Mathlib
import Definitions.Def_AgencyPassThrough_Pricing_Model

namespace AgencyPassThrough.Pricing

/-- Proposition 1, p. 12, and its identity in Appendix B, p. 26. -/
theorem proposition_1 (n : ℕ) (hn : 2 ≤ n) (eps a b : ℝ)
    (heps0 : 0 ≤ eps) (heps1 : eps < 1) (hab : 0 < a - eps * b) :
    thetaW n eps a b - thetaB eps =
      (1 - eps) * ((n : ℝ) - 1 + eps) * b / (a - eps * b) ∧
    (thetaW n eps a b < thetaB eps ↔ b < 0) ∧
    (0 ≤ b → thetaB eps ≤ thetaW n eps a b) := by sorry

end AgencyPassThrough.Pricing
