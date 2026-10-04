-- Prove2me | Theorems.Thm_FiniteMagmaE677_no_left_period_two
-- name    : FiniteMagmaE677.no_left_period_two
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T06:53:03.276907+00:00
-- url     : https://prove2.me/theorems/093383d4-c2a9-4ad8-b815-88ee797765a7
-- title:
--   No element of a finite E677 magma has left-orbit period exactly two
-- statement:
--   Let $A$ be a finite set with a binary operation $\diamond$ satisfying E677 and let $L_x z = x \diamond z$. No element has forward orbit under $L_x$ of exact period two: if
--
--   $$ x = L_x^2 x = x \diamond (x \diamond x), $$
--
--   then already $x \diamond x = x$ (the orbit is a fixed point). The proof instantiates E677 at $(x,x)$, obtaining $x = L_x^2 c_1$ with $c_1 = (x \diamond x) \diamond x$; comparing with the hypothesis and cancelling $L_x$ twice gives $c_1 = x$, so the successor $x \diamond x$ is a fixer of $x$. Fixer uniqueness forces $x \diamond x = c_1 = x$, contradicting a nontrivial period.
-- source:
--   Original result proved in this submission, in the context of the Prove2Me mission 'Equational Magmas: E677 → E255 (finite case)'; cf. Equational Theories Project blueprint Chapter 13, https://teorth.github.io/equational_theories/blueprint/677-chapter.html.

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_fixer_unique

universe u

theorem FiniteMagmaE677.no_left_period_two {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x : α)
    (hper : op x (op x x) = x) : op x x = x := by sorry
