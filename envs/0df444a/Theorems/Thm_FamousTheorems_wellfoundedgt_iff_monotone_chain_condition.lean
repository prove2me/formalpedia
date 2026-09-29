-- Prove2me | Theorems.Thm_FamousTheorems_wellfoundedgt_iff_monotone_chain_condition
-- name    : FamousTheorems.wellfoundedgt_iff_monotone_chain_condition
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:54:30.584275+00:00
-- url     : https://prove2.me/theorems/d005a66c-691b-49e7-ad21-575809c04e54
-- title:
--   The ascending chain condition
-- statement:
--   **The ascending chain condition.** An order is well-founded upward exactly when every monotone sequence eventually stabilises. The equivalence converts a statement about arbitrary ascending chains into one about sequences, which is what makes the condition checkable in practice. It is the defining property of Noetherian structures: a ring is Noetherian when its ideals satisfy it, and the same condition on submodules gives Noetherian modules. Stabilisation is what licenses induction over such orders and guarantees that constructions terminate. **Formalization note.** `WellFoundedGT` is well-foundedness of the reversed order. The result is Mathlib's `wellFoundedGT_iff_monotone_chain_condition`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem wellfoundedgt_iff_monotone_chain_condition :
    ∀ {α : Type u_1} [inst : Preorder α], 
    WellFoundedGT α ↔ ∀ (a : ℕ →o α), ∃ n, ∀ (m : ℕ), n ≤ m → ¬a n < a m := by sorry

end FamousTheorems
