-- Prove2me | Theorems.Thm_CustAssort_Value_eq_3_1
-- name    : CustAssort.Value.eq_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:05.098867+00:00
-- url     : https://prove2.me/theorems/eccc8885-5db4-4ba2-94de-4c294002c9af
-- title:
--   Equation (3.1), p. 8 — split weighted MNL revenue by the diagonal product
-- statement:
--   On the paper's instance with $a>0$ and $b\ge0$, let $S$ be any assortment and $j$ any customer type. Separate the numerator of $\theta_j\operatorname{Rev}_j(S)$ into products $i<j$ and the possible product $j$. Equation (3.1) is
--
--   $$\theta_j\operatorname{Rev}_j(S)=\theta_j\frac{\sum_{i\in S,\ i<j}a^i b^{m-i+1}}{1+\sum_{i\in S,\ i\le j}b^{m-i+1}}+\alpha\frac{\mathbf1_{\{j\in S\}}b^{m-j+1}}{1+\sum_{i\in S,\ i\le j}b^{m-i+1}}.$$
--
--   This decomposition isolates the two contributions bounded separately in the proof of Theorem 3.1.
--
--   **Formalization Note** `firstTerm` and `secondTerm` are the two displayed fractions. The paper's indices start at one; Lean's start at zero, so $i\le j-1$ is `i < j`.
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082 (version of December 7, 2021), p. 8, (3.1)

import Mathlib
import Definitions.Def_CustAssort_Value_Setting

namespace CustAssort.Value

/-- Equation (3.1), page 8: the weighted type revenue splits before and at `j`. -/
theorem eq_3_1 (m : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (S : Finset (Fin m)) (j : Fin m) :
    thetaI a m j * CustAssort.AugGreedy.rev (vI b m) (revI a m) j S =
      firstTerm a b S j + secondTerm a b S j := by sorry

end CustAssort.Value
