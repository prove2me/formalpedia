-- Prove2me | Theorems.Thm_CustAssort_Value_thm31_first_term
-- name    : CustAssort.Value.thm31_first_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:39.12964+00:00
-- url     : https://prove2.me/theorems/254f076b-7378-48eb-b2a2-76fa661c6423
-- title:
--   Proof of Theorem 3.1, p. 8 — the earlier-product term is at most 2αb^m/a
-- statement:
--   On the paper's instance with $a\ge2$ and $b\ge1$, for every assortment $S$ and customer type $j$, the earlier-product term in equation (3.1) obeys
--
--   $$\theta_j\frac{\sum_{i\in S,\ i<j}a^i b^{m-i+1}}{1+\sum_{i\in S,\ i\le j}b^{m-i+1}}\le\frac{2\alpha b^m}{a}.$$
--
--   This is the first uniform contribution to the MMNL upper bound in Theorem 3.1.
--
--   **Formalization Note** The sum is empty for the first customer type. The natural-number exponents in Lean include the shift from the paper's one-based indices.
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082 (version of December 7, 2021), p. 8, proof of Theorem 3.1, first-term display after (3.1)

import Mathlib
import Definitions.Def_CustAssort_Value_Setting

namespace CustAssort.Value

/-- The first-term bound following equation (3.1), page 8. -/
theorem thm31_first_term (m : ℕ) (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (S : Finset (Fin m)) (j : Fin m) :
    firstTerm a b S j ≤ 2 * alpha a m * b ^ m / a := by sorry

end CustAssort.Value
