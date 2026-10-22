-- Prove2me | Theorems.Thm_FiniteMagmaE677_eq_of_e677_ops_agree_off_one_row
-- name    : FiniteMagmaE677.eq_of_e677_ops_agree_off_one_row
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-20T22:47:24.722725+00:00
-- url     : https://prove2.me/theorems/e0f0eb45-4234-4498-bb30-34b10122cabf
-- title:
--   Counterexample structure (c) — Two E677 tables that agree off one row are equal
-- statement:
--   Let $\cdot$ and $\star$ be two operations on the same finite set $M$, both satisfying E677. Suppose that $u\star v=u\cdot v$ for every $u\ne a$ and every $v$, so that the two tables can differ only in the row of $a$. Then $\star=\cdot$. Neither operation is assumed to satisfy E255.
--
--   So a search that changes one row of a finite E677 table never reaches a different E677 table; in particular, no counterexample is one row away from an E677 table that satisfies E255.
--
--   Related results. In one finite E677 table, two rows are never equal: if $a\cdot x=b\cdot x$ for every $x$, then $a=b$ (I. Tencer, ETP Zulip thread "FINITE: 677 -> 255", 2024-12-21; also J. Hyun, same thread, 2026-05-17). The statement above compares two tables. The two-table statement was not found in the sources searched: the ETP blueprint, the ETP paper (arXiv:2512.07087v2) and the ETP Zulip thread up to 2026-10-14.
-- source:
--   Adam McKenna, private repo, 2026-10-20: Lean theorem Eq677.eq_of_rows_eq_except (lean/E677/RowRigidity.lean)

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.eq_of_e677_ops_agree_off_one_row
{α : Type u} [Finite α] (op op' : α → α → α)
(h : FiniteMagmaE677.E677 op) (h' : FiniteMagmaE677.E677 op') (a : α)
(hrows : ∀ u : α, u ≠ a → ∀ v : α, op' u v = op u v) :
op' = op := by sorry
