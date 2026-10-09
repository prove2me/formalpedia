-- Prove2me | Theorems.Thm_CustAssort_Value_thm31_second_term
-- name    : CustAssort.Value.thm31_second_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:19.332047+00:00
-- url     : https://prove2.me/theorems/98213230-cecb-43a8-8110-2bd43328be53
-- title:
--   Proof of Theorem 3.1, p. 8 — the diagonal term decays from the smallest product
-- statement:
--   On the paper's instance with $a>0$ and $b\ge1$, let $S$ be a nonempty assortment, let $\ell_S$ be its smallest product index, and take $j\in S$. The diagonal-product term in equation (3.1) satisfies
--
--   $$\alpha\frac{b^{m-j+1}}{1+\sum_{i\in S,\ i\le j}b^{m-i+1}}\le\frac{\alpha}{b^{j-\ell_S}}.$$
--
--   This is the second contribution to the MMNL upper bound. For $j\notin S$ the diagonal term is zero.
--
--   **Formalization Note** Both $j$ and $\ell_S$ are 0-based in Lean, so their difference remains $j-\ell_S$. Membership $j\in S$ ensures this exponent is nonnegative.
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082 (version of December 7, 2021), p. 8, proof of Theorem 3.1, second-term display after (3.1)

import Mathlib
import Definitions.Def_CustAssort_Value_Setting

namespace CustAssort.Value

/-- The second-term bound following equation (3.1), page 8. -/
theorem thm31_second_term (m : ℕ) (a b : ℝ) (hb : 1 ≤ b) (ha : 0 < a)
    (S : Finset (Fin m)) (hS : S.Nonempty) (j : Fin m) (hj : j ∈ S) :
    secondTerm a b S j ≤ alpha a m / b ^ (j.val - (S.min' hS).val) := by sorry

end CustAssort.Value
