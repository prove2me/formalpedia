-- Prove2me | Theorems.Thm_CustAssort_Value_thm31_type_bound
-- name    : CustAssort.Value.thm31_type_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:28.388019+00:00
-- url     : https://prove2.me/theorems/1138d10e-a4ac-4273-9a6e-5abbd2ae6c40
-- title:
--   Proof of Theorem 3.1, p. 7 — a type contribution is bounded by the MMNL optimum
-- statement:
--   Fix positive product revenues, nonnegative preference weights, nonnegative type arrival weights, and a cardinality budget $K$. For any customer type $q$ and any carried set $S$ with $|S|\le K$, its personalized expected contribution satisfies
--
--   $$\theta_q f_q(S)\le z_{\rm MMNL}.$$
--
--   The type-optimal subassortment is feasible as a common MMNL offer, whose other type contributions are nonnegative. This is the typewise comparison used for the upper bound in Theorem 3.1.
--
--   **Formalization Note** The source applies this comparison to a CAP-optimal $S^*$; the statement records the same comparison for every feasible $S$. Normalization of $\theta$ is not needed for this intermediate inequality.
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082 (version of December 7, 2021), p. 7, proof of Theorem 3.1, displayed type-q comparison

import Mathlib
import Definitions.Def_CustAssort_Value_Setting

namespace CustAssort.Value

/-- The typewise upper bound in the proof of Theorem 3.1, page 7. -/
theorem thm31_type_bound {n m : ℕ} (K : ℕ) (r : Fin n → ℝ)
    (v : Fin n → Fin m → ℝ) (θ : Fin m → ℝ)
    (hr : ∀ i, 0 < r i) (hv : ∀ i j, 0 ≤ v i j) (hθ : ∀ j, 0 ≤ θ j) :
    ∀ (q : Fin m) (S : Finset (Fin n)), S.card ≤ K →
      θ q * CustAssort.AugGreedy.fj v r q S ≤ zMMNL θ v r K := by sorry

end CustAssort.Value
