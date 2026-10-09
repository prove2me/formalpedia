-- Prove2me | Theorems.Thm_CustAssort_AugGreedy_appC_monotonicity
-- name    : CustAssort.AugGreedy.appC_monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:24.47354+00:00
-- url     : https://prove2.me/theorems/03a94154-67c7-40ba-af54-5dcd3af9a294
-- title:
--   Appendix C, Monotonicity — personalized revenue increases with availability
-- statement:
--   Fix a customer type $j$ and two sets of available products $A\subseteq B$. Let $f_j(S)$ be the largest MNL expected revenue obtainable by offering a subset of $S$. Then
--   $$
--   f_j(A)\le f_j(B).
--   $$
--   The statement records the monotonicity used for the truncation analysis and Theorem 4.2.
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082, https://ssrn.com/abstract=3830082 (version of December 7, 2021), App. C, Monotonicity, p. 36

import Mathlib
import Definitions.Def_CustAssort_AugGreedy_Setting

namespace CustAssort.AugGreedy

/-- Appendix C, Monotonicity, p. 36: making more products available cannot reduce a type's optimized revenue. -/
theorem appC_monotonicity {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (j : Fin m) (A B : Finset (Fin n)) (hAB : A ⊆ B) :
    fj v r j A ≤ fj v r j B := by sorry

end CustAssort.AugGreedy
