-- Prove2me | Theorems.Thm_FamousTheorems_himp_eq_top_iff
-- name    : FamousTheorems.himp_eq_top_iff
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:54:31.159181+00:00
-- url     : https://prove2.me/theorems/4767b245-0f9f-4b7a-ae07-8f9fa01bae9e
-- title:
--   The deduction theorem
-- statement:
--   **The deduction theorem** in Heyting algebra form. The implication $a \Rightarrow b$ is the top element exactly when $a \le b$. Reading the order as entailment, this says $b$ is derivable from $a$ precisely when the implication is a theorem, which is the algebraic content of the deduction theorem of propositional logic: discharging a hypothesis and asserting an implication are interchangeable. It is the adjunction defining Heyting implication, and it is what makes Heyting algebras the algebraic semantics of intuitionistic logic. **Formalization note.** `himp` is Heyting implication and `⊤` the top element. The result is Mathlib's `himp_eq_top_iff`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem himp_eq_top_iff :
    ∀ {α : Type u_1} [inst : GeneralizedHeytingAlgebra α] {a b : α}, a ⇨ b = ⊤ ↔ a ≤ b := by sorry

end FamousTheorems
