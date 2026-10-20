-- Prove2me | Theorems.Thm_AgencyPassThrough_Pricing_proposition_2
-- name    : AgencyPassThrough.Pricing.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:47.222269+00:00
-- url     : https://prove2.me/theorems/10ca5079-b64b-46fc-9a33-9a1efb4f3988
-- title:
--   Proposition 2 — agency versus wholesale under cross-brand pass-through
-- statement:
--   Consider $n\geq2$ competing suppliers with unit cost $c_s\geq0$, diversion ratio $0\leq\epsilon<1$, own-brand pass-through $a$, and cross-brand pass-through $b$. Let $p^W,p^B$ be any prices in the demand domain satisfying the wholesale and agency equations of Lemma 1. The own- and cross-brand rates also obey the paper's total pass-through identity.
--
--   If $b\geq0$, then
--
--   $$p^B\leq p^W,\qquad \pi_r^B\geq\pi_r^W,\qquad \pi_i^B\leq\pi_i^W.$$
--
--   If $b<0$, then the retail price is lower under wholesale selling exactly when
--
--   $$p^W<p^B\quad\Longleftrightarrow\quad\theta^W<\theta^B\min\{K^B,1\}.$$
--
--   This is Proposition 2's comparison of channel prices and profits, with the specific equilibrium values quantified rather than chosen by the theorem.
--
--   **Formalization Note** The n-product games are represented by their Lemma 1 equilibrium equations after normalizing the e-tailer's unit cost to zero. The claims that one contract *can* make an agent better off in part (ii) are existence claims illustrated by the paper's examples and are outside this theorem. Positivity of $a-\epsilon b$ and $p^B-\theta^B\lambda(p^B)$, and $\theta^W\in[0,1]$, guard the paper's divisions and slope comparison.
-- source:
--   Hu, Zheng & Pan, Agency or Wholesale? The Role of Retail Pass-Through, SSRN preprint 3724934 (2021 revision, PDF sha256 1ab91ed8…), p. 13, Proposition 2(i) and price criterion of 2(ii)

import Mathlib
import Definitions.Def_AgencyPassThrough_Pricing_Model

namespace AgencyPassThrough.Pricing

/-- Proposition 2, p. 13, with the existence claims set aside as in the mission brief. -/
theorem proposition_2 (q : ℝ → ℝ) (D : Set ℝ) (hq : DemandStanding q D)
    (n : ℕ) (hn : 2 ≤ n) (cs eps a b pW pB : ℝ)
    (hcs : 0 ≤ cs) (heps0 : 0 ≤ eps) (heps1 : eps < 1)
    (hab : 0 < a - eps * b)
    (hdpdw : a + ((n : ℝ) - 1) * b = 1 / (1 - deriv (lam q) pW))
    (hθW0 : 0 ≤ thetaW n eps a b) (hθW1 : thetaW n eps a b ≤ 1)
    (hW : IsWholesaleEq q D cs (thetaW n eps a b) pW)
    (hB : IsAgencyEq q D cs (thetaB eps) pB) :
    (0 ≤ b → pB ≤ pW ∧
      piWr n q pW ≤ piBr n q cs (thetaB eps) pB ∧
      piBi q cs (thetaB eps) pB ≤ piWi q cs pW) ∧
    (b < 0 → (pW < pB ↔
      thetaW n eps a b < thetaB eps * min (KB q cs (thetaB eps) pB) 1)) := by sorry

end AgencyPassThrough.Pricing
