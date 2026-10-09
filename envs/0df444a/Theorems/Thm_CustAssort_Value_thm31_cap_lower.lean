-- Prove2me | Theorems.Thm_CustAssort_Value_thm31_cap_lower
-- name    : CustAssort.Value.thm31_cap_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:47.690592+00:00
-- url     : https://prove2.me/theorems/ed317faa-bcb7-4199-9f1b-61b85fae9fdb
-- title:
--   Proof of Theorem 3.1, p. 8 — the tightness instance has CAP value at least αm/2
-- statement:
--   In the paper's instance with $m\ge1$ products and types, parameter $a>0$, and parameter $b\ge1$, let $\alpha=(\sum_{j=1}^m a^{-j})^{-1}$. Then
--
--   $$z_{\rm CAP}\ge\frac{\alpha m}{2}.$$
--
--   This is the customized-revenue side of the explicit family showing that the factor $m$ in Theorem 3.1 has the right order.
--
--   **Formalization Note** The instance has $n=K=m$ and uses the paper's $r_i=a^i$, $\theta_j=\alpha/a^j$, and $v_{ij}=b^{m-i+1}$ for $i\le j$ (zero otherwise).
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082 (version of December 7, 2021), p. 8, proof of Theorem 3.1, display z_CAP ≥ α·m/2

import Mathlib
import Definitions.Def_CustAssort_Value_Setting

namespace CustAssort.Value

/-- The personalized-revenue lower bound in the proof of Theorem 3.1, page 8. -/
theorem thm31_cap_lower (m : ℕ) (a b : ℝ)
    (hm : 1 ≤ m) (ha : 0 < a) (hb : 1 ≤ b) :
    alpha a m * (m : ℝ) / 2 ≤ zCAP (thetaI a m) (vI b m) (revI a m) m := by sorry

end CustAssort.Value
