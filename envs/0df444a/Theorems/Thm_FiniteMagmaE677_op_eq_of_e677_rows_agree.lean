-- Prove2me | Theorems.Thm_FiniteMagmaE677_op_eq_of_e677_rows_agree
-- name    : FiniteMagmaE677.op_eq_of_e677_rows_agree
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-20T22:48:49.720774+00:00
-- url     : https://prove2.me/theorems/7a58a1f4-6292-408f-a4c3-c17e43082d7e
-- title:
--   Counterexample structure (d) — Support rule for changed rows
-- statement:
--   Let $\cdot$ and $\star$ be two operations on the same finite set, both satisfying E677. Suppose that the rows of $b$ and of $t$ are the same in both tables, $b\star y=b\cdot y$ and $t\star y=t\cdot y$ for every $y$, and that $b\cdot t=a$. Then $a\star b=a\cdot b$.
--
--   So if a set $S$ contains every row that changes and $b\notin S$, a changed cell $(a,b)$ needs the old preimage $t$ of $a$ under left multiplication by $b$ to lie in $S$. This limits the cells that a change of an E677 table can touch.
--
--   Known ingredient. E677 for $\cdot$ at $x=t$, $y=b$ gives $L_b^{-1}(t)=t\cdot((b\cdot t)\cdot b)$, where $L_b$ is left multiplication by $b$ (ETP blueprint Lemma 13.1(i)). So $a\cdot b=(b\cdot t)\cdot b=L_t^{-1}(L_b^{-1}(t))$: in one table, the entry $a\cdot b$ is fixed by the rows of $b$ and $t$. T. Tao (ETP Zulip thread "FINITE: 677 -> 255", 2024-12-11, and again 2024-12-14) wrote E677 as the two equations $f(x,y)=(y\cdot x)\cdot y$ and $x=y\cdot(x\cdot f(x,y))$ and noted that both "assert that one entry in the multiplication table propagates to another"; the one-table fact above uses both of them. The statement above follows when this fact is applied to both tables. The two-table statement was not found in the sources searched: the ETP blueprint, the ETP paper (arXiv:2512.07087v2) and the ETP Zulip thread up to 2026-10-14.
-- source:
--   Adam McKenna, private repo, 2026-10-20: Lean theorem Eq677.op_eq_op_of_rows_eq (lean/E677/RowRigidity.lean)

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.op_eq_of_e677_rows_agree
{α : Type u} [Finite α] (op op' : α → α → α)
(h : FiniteMagmaE677.E677 op) (h' : FiniteMagmaE677.E677 op') (a b t : α)
(hb : ∀ y : α, op' b y = op b y) (ht : ∀ y : α, op' t y = op t y)
(hbt : op b t = a) :
op' a b = op a b := by sorry
