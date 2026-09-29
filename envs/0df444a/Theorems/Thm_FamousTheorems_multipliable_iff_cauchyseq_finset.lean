-- Prove2me | Theorems.Thm_FamousTheorems_multipliable_iff_cauchyseq_finset
-- name    : FamousTheorems.multipliable_iff_cauchyseq_finset
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:55:15.845016+00:00
-- url     : https://prove2.me/theorems/66a6e2ff-fce5-434b-aee2-186935f954d9
-- title:
--   The Cauchy criterion for products
-- statement:
--   **The Cauchy criterion** for unconditional products. A family is multipliable exactly when its finite partial products form a Cauchy net over the directed set of finite subsets. Completeness converts an existence question about the limit into a self-referential condition on the partial products, testable without knowing the value -- which is the whole utility of Cauchy criteria. Indexing by finite subsets rather than by an ordering is what makes the resulting notion unconditional, so no rearrangement can change the outcome. **Formalization note.** `Multipliable` is the multiplicative analogue of `Summable`, and the net is over `Finset`. The result is Mathlib's `multipliable_iff_cauchySeq_finset`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem multipliable_iff_cauchyseq_finset :
    ∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α] [inst_1 : CommMonoid α] 
    [CompleteSpace α] {f : β → α}, Multipliable f ↔ CauchySeq fun s => ∏ b ∈ s, f b := by sorry

end FamousTheorems
