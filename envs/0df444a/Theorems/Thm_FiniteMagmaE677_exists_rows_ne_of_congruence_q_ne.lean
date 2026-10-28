-- Prove2me | Theorems.Thm_FiniteMagmaE677_exists_rows_ne_of_congruence_q_ne
-- name    : FiniteMagmaE677.exists_rows_ne_of_congruence_q_ne
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-21T04:48:57.931685+00:00
-- url     : https://prove2.me/theorems/e2455ca7-616b-4ddf-828f-73fa78a87467
-- title:
--   Counterexample structure (g) — Fixer block: a pointwise form of Tao's row-agreement argument (Lean formalization)
-- statement:
--   Let $(M,\diamond)$ be a finite magma that satisfies E677 and let $\theta$ be a congruence of $(M,\diamond)$. Let $z\in M$ satisfy $((z\diamond z)\diamond z)\diamond z\ne z$ and $((z\diamond z)\diamond z)\diamond z\;\theta\;z$, and put $s=(z\diamond z)\diamond z$. Then there are $a\ne a'$ in the $\theta$-class of $s$ and $u$ in the $\theta$-class of $z$ with $a\diamond z=a'\diamond z$ and $a\diamond u\ne a'\diamond u$.
--
--   So at each point where E255 fails, a counterexample has two rows that agree in one column and differ in another column of the same class. In the other direction: if any two rows from the class of $s$ that agree in column $z$ agree on the whole class of $z$, then E255 holds at $z$.
--
--   Attribution. The argument is T. Tao's (ETP Zulip thread "FINITE: 677 -> 255", 2024-12-14). He stated it for extension models $(x,s)\diamond(y,t)=(x\diamond y,s\diamond_{x,y}t)$ over a base that satisfies E255: if left multiplications in one fibre that agree at one point agree everywhere, the right multiplications are injective and E255 follows, "so we need operations $\diamond_{x,y}$ for which left-multiplication by different elements $s,s'$ can agree in some locations but not in others." The step that the rows of the fixer block are pairwise distinct is B. Le Floch's argument for piecewise affine extensions (same thread, 2024-12-14), which Tao's message states for all extension models. This theorem is a pointwise form of Tao's argument: one point $z$, one pair of classes, and a hypothesis on the quotient only at $z$. All classes of $\theta$ have the same size (M. Bonatto and D. Stanovský, arXiv:1902.08980v3).
-- source:
--   Adam McKenna, private repo, 2026-10-20: Lean theorem E677Crit.exists_rows_ne_of_q_ne (lean/E677/FixerBlock.lean); argument by T. Tao, ETP Zulip thread "FINITE: 677 -> 255", 2024-12-14

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.exists_rows_ne_of_congruence_q_ne
{α : Type u} [Finite α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(r : α → α → Prop) (hr : Equivalence r)
(hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
(z : α) (hz : op (op (op z z) z) z ≠ z)
(hrz : r (op (op (op z z) z) z) z) :
∃ a a' u : α, r (op (op z z) z) a ∧ r (op (op z z) z) a' ∧ r z u ∧
  a ≠ a' ∧ op a z = op a' z ∧ op a u ≠ op a' u := by sorry
