-- Prove2me | Theorems.Thm_CustAssort_Value_thm31_mmnl_upper
-- name    : CustAssort.Value.thm31_mmnl_upper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:53.947018+00:00
-- url     : https://prove2.me/theorems/5a7bc6a5-3593-4233-8cf4-b861a56f2200
-- title:
--   Proof of Theorem 3.1, p. 9 — the tightness instance has MMNL value at most 3α
-- statement:
--   In the paper's explicit instance with $m\ge2$, choose $b=m-1$ and $a=2m(m-1)^m$. Every common assortment $S$ has weighted expected revenue at most $3\alpha$, and therefore
--
--   $$z_{\rm MMNL}\le3\alpha.$$
--
--   Together with the customized lower bound $z_{\rm CAP}\ge\alpha m/2$, this bounds the MMNL value on the tightness family.
--
--   **Formalization Note** The theorem states both the bound for each $S$ and its finite maximum. The condition $m\ge2$ gives $b\ge1$ and $a\ge2$.
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082 (version of December 7, 2021), p. 9, proof of Theorem 3.1, displays and choice of a,b

import Mathlib
import Definitions.Def_CustAssort_Value_Setting

namespace CustAssort.Value

/-- The `3α` common-assortment bound in the proof of Theorem 3.1, page 9. -/
theorem thm31_mmnl_upper (m : ℕ) (hm : 2 ≤ m) :
    (∀ S : Finset (Fin m),
      (∑ j : Fin m, thetaI (aStar m) m j *
        CustAssort.AugGreedy.rev (vI (bStar m) m) (revI (aStar m) m) j S) ≤
        3 * alpha (aStar m) m) ∧
      zMMNL (thetaI (aStar m) m) (vI (bStar m) m)
        (revI (aStar m) m) m ≤ 3 * alpha (aStar m) m := by sorry

end CustAssort.Value
