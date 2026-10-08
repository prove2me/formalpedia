-- Prove2me | Theorems.Thm_Conway99Formal_TriangleBound_unordered_pair_double_count
-- name    : Conway99Formal.TriangleBound.unordered_pair_double_count
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T06:44:55.013819+00:00
-- url     : https://prove2.me/theorems/952b29db-5883-406a-8542-b46b8b071f53
-- title:
--   Unordered pair double count
-- statement:
--   For a finite set and a symmetric relation, the ordered count of related distinct pairs is twice the count of related unordered two-element subsets.
-- source:
--   blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/triangle-bound/GraphCounts.lean#L26-L114

import Mathlib

namespace Conway99Formal.TriangleBound
end Conway99Formal.TriangleBound

set_option autoImplicit false

/-! Literal graph counts for the universal triangle and prism claim. -/

open Conway99Formal.TriangleBound

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem Conway99Formal.TriangleBound.unordered_pair_double_count {A : Type*} [Fintype A] [DecidableEq A]
    (s : Finset A) (R : A → A → Prop) [DecidableRel R]
    (hsym : ∀ a b, R a b → R b a) :
    (∑ a ∈ s, (s.filter fun b => a ≠ b ∧ R a b).card) =
      2 * ((s.powersetCard 2).filter fun p =>
        ∃ a b, a ∈ p ∧ b ∈ p ∧ a ≠ b ∧ R a b).card := by sorry
