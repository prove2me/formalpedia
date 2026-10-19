-- Prove2me | Theorems.Thm_FiniteMagmaE677_fixer_exists
-- name    : FiniteMagmaE677.fixer_exists
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-10T06:37:21.091009+00:00
-- url     : https://prove2.me/theorems/5e853f45-1097-413e-9425-17c8933186e0
-- title:
--   Fixer existence: an equivalent form of the main target
-- statement:
--   Fixer-existence form of the main target. Let $\alpha$ be a finite type with an arbitrary total operation $\diamond$ satisfying E677. The assertion is
--
--   $$\forall x\in\alpha,\quad \exists y\in\alpha,\quad y\diamond x=x.$$
--
--   For finite E677 magmas this is the same obligation as E255 (blueprint Lemma 13.2): E255 at $x$ supplies the fixer $(x\diamond x)\diamond x$, and from any fixer $y$ of $x$ the fixer-determination theorem gives $y=(x\diamond x)\diamond x$, hence E255 at $x$. It is retained as an explicit reduction dependency, not as a smaller milestone.
-- source:
--   Matthew Bolan et al., The Equational Theories Project: Advancing Collaborative Mathematical Research at Scale, arXiv:2512.07087v2 (December 16, 2025), Section 8, Problem 8.1, https://arxiv.org/html/2512.07087v2

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.fixer_exists {α : Type u} [Fintype α] (op : α → α → α)
    (h : FiniteMagmaE677.E677 op) (x : α) : ∃ y : α, op y x = x := by sorry
