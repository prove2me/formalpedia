-- Prove2me | Theorems.Thm_FamousTheorems_cisup_mem_iinter_icc_of_antitone
-- name    : FamousTheorems.cisup_mem_iinter_icc_of_antitone
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:54:49.077087+00:00
-- url     : https://prove2.me/theorems/8e5feca2-594a-4f53-a87c-c460d3408dd4
-- title:
--   The nested intervals lemma
-- statement:
--   **The nested interval lemma.** A decreasing sequence of nonempty closed intervals in a conditionally complete order has a point in every one of them, namely the supremum of the left endpoints. Completeness is what supplies the point; the same statement fails over the rationals, where nested intervals can close in on an irrational and leave the intersection empty. This is one of the standard equivalents of completeness of the reals and the mechanism behind bisection arguments, including the usual proofs of Bolzano-Weierstrass and of the intermediate value theorem. **Formalization note.** The endpoints are monotone and antitone respectively, and the conclusion places `⨆ a` in every interval. The result is Mathlib's `Monotone.ciSup_mem_iInter_Icc_of_antitone`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem cisup_mem_iinter_icc_of_antitone :
    ∀ {α : Type u_1} {β : Type u_2} 
    [inst : ConditionallyCompletePartialOrderSup α] [inst_1 : Preorder β] [IsDirectedOrder β] {f g : β → α}, 
    Monotone f → Antitone g → f ≤ g → ⨆ n, f n ∈ ⋂ n, Icc (f n) (g n) := by sorry

end FamousTheorems
