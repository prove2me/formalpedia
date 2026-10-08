-- Prove2me | Theorems.Thm_ConstrNestedLogit_Space_theorem_6
-- name    : ConstrNestedLogit.Space.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:45.321975+00:00
-- url     : https://prove2.me/theorems/a5503509-373f-43bb-9c05-fbdab12b0c58
-- title:
--   Theorem 6: quadratic candidate family with factor two
-- statement:
--   For a nest with space constraints, there is a single collection $\mathcal A_i$ containing all singleton assortments and rounded optima of the LP relaxation of (10). Every member is feasible, and
--
--   $$|\mathcal A_i|\le(n+1)^2,\qquad \forall u\ge0\ \exists S\in\mathcal A_i:\ \forall T\in C_i,\ V_i(T)(R_i(T)-u)\le2V_i(S)(R_i(S)-u).$$
--
--   This gives an explicit quadratic bound for Theorem 6's $O(n^2)$ collection and supports the overall assortment guarantee through Theorem 4.
--
--   **Formalization Note** Products form a nonempty finite set. The paper's implicit positive preference and space weights are stated explicitly.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 21, Theorem 6

import Mathlib
import Definitions.Def_ConstrNestedLogit_Space_Model

namespace ConstrNestedLogit.Space

/-- Theorem 6, with the explicit quadratic bound supplied by the line arrangement. -/
theorem theorem_6 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hn : 0 < n)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ j, 0 < I.v i j)
    (hw : ∀ j, 0 < w i j) (hwc : ∀ j, w i j ≤ c i) :
    ∃ A : Finset (Finset (Fin n)),
      isRoundedCandidateFamily I w c i A ∧
      (∀ S ∈ A, spaceFeasible w c i S) ∧
      A.card ≤ (n + 1) ^ 2 ∧
      ∀ u : ℝ, 0 ≤ u → ∃ S ∈ A, isApproximateAt I w c i u 2 S := by sorry

end ConstrNestedLogit.Space
