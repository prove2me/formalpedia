-- Prove2me | Theorems.Thm_FiniteMagmaE677_two_rows_differ_of_e677_ops_ne
-- name    : FiniteMagmaE677.two_rows_differ_of_e677_ops_ne
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-20T22:50:14.897372+00:00
-- url     : https://prove2.me/theorems/714c575e-5900-449b-994c-5e6185db7872
-- title:
--   Counterexample structure (e) — Two different E677 tables differ in at least two rows
-- statement:
--   Let $\cdot$ and $\star$ be two different operations on the same finite set, both satisfying E677. Then there are elements $a_1\ne a_2$ whose rows both change: $a_1\star v\ne a_1\cdot v$ for some $v$ and $a_2\star w\ne a_2\cdot w$ for some $w$.
--
--   This follows from Counterexample structure (c): if only one row changed, (c) would give $\star=\cdot$. See (c) for related results.
-- source:
--   Adam McKenna, private repo, 2026-10-20: Lean theorem Eq677.exists_two_rows_ne (lean/E677/RowRigidity.lean)

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.two_rows_differ_of_e677_ops_ne
{α : Type u} [Finite α] (op op' : α → α → α)
(h : FiniteMagmaE677.E677 op) (h' : FiniteMagmaE677.E677 op') (hne : op' ≠ op) :
∃ a₁ a₂ : α, a₁ ≠ a₂ ∧ (∃ v : α, op' a₁ v ≠ op a₁ v) ∧
  ∃ v : α, op' a₂ v ≠ op a₂ v := by sorry
