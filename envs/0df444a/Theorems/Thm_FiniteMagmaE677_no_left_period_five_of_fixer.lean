-- Prove2me | Theorems.Thm_FiniteMagmaE677_no_left_period_five_of_fixer
-- name    : FiniteMagmaE677.no_left_period_five_of_fixer
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-26T01:57:08.551115+00:00
-- url     : https://prove2.me/theorems/ef8ad662-742c-43ba-bae0-2e95204fac5d
-- title:
--   A fixer excludes exact left period 5 in a finite E677 magma
-- statement:
--   Let $M$ be a finite set with a binary operation $\diamond$ satisfying
--
--   $$z=y\diamond\bigl(z\diamond((y\diamond z)\diamond y)\bigr)\qquad(z,y\in M).$$
--
--   Fix $x\in M$ and put $L_x(z)=x\diamond z$. Suppose that $x$ has a fixer and returns after 5 applications of its own left translation:
--
--   $$\exists w\in M,\quad w\diamond x=x,\qquad L_x^5(x)=x.$$
--
--   Then
--
--   $$x\diamond x=x.$$
--
--   Thus a point satisfying E255 cannot have an exact left period of 5. The fixer hypothesis is essential to the scope of this assertion: this statement does not exclude period 5 at a point where E255 fails. It supplies a structural constraint for the fixed outsider seed in the period-four collision branches.
-- source:
--   Original auxiliary deduction for Prove2Me milestone D4.3b, https://prove2.me/theorems/98f7dc30-3fa6-4160-89d8-62bd30c5e338, 2026-10-26. Uses E677 and the finite left-cancellation, fixer-uniqueness and backward-recurrence identities in Equational Theories Project, Chapter 13, Lemma 13.1(i)-(iii), https://teorth.github.io/equational_theories/blueprint/677-chapter.html. The extra short-period conclusion is derived in the accompanying proof, not quoted from the blueprint.

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.no_left_period_five_of_fixer {α : Type u} [Fintype α] (op : α → α → α)
    (h : FiniteMagmaE677.E677 op) (x : α)
    (hper : op x (op x (op x (op x (op x (x))))) = x)
    (hfix : FiniteMagmaE677.HasFixerAt op x) : op x x = x := by sorry
