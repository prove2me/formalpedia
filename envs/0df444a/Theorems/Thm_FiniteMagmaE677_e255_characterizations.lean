-- Prove2me | Theorems.Thm_FiniteMagmaE677_e255_characterizations
-- name    : FiniteMagmaE677.e255_characterizations
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T13:52:47.451277+00:00
-- url     : https://prove2.me/theorems/e49770ef-0363-4681-91e6-e55c438e8d72
-- title:
--   Six equivalent characterizations of equation 255 at an element
-- statement:
--   Let $x$ be an element of a finite set with a binary operation $\diamond$ satisfying E677, and write $S y = y \diamond y$. The following six statements are equivalent:
--
--   1. $x = ((x \diamond x) \diamond x) \diamond x$ (equation 255 holds at $x$);
--   2. $x$ has a fixer: there is $y$ with $y \diamond x = x$;
--   3. there is $w$ with $(x \diamond w) \diamond x = x$;
--   4. there is $z$ with $x \diamond (z \diamond x) = z$;
--   5. there is $y$ with $(x \diamond y) \diamond x = y$;
--   6. there is $y$ with $x \diamond (y \diamond y) = y$.
--
--   Together with fixer uniqueness (the fixer, when it exists, equals $(x \diamond x) \diamond x$), this is the finite-magma form of the Equational Theories Project blueprint's lemma on equivalent characterizations of equation 255. Every implication is one or two instances of E677 plus left cancellations, so each of the six shapes is a valid certificate of 255 at $x$.
-- source:
--   Equational Theories Project, online proof blueprint, Chapter 13 (677), equivalence lemma for 255, https://teorth.github.io/equational_theories/blueprint/677-chapter.html; Lean proof contributed here.

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_fixer_unique

universe u

theorem FiniteMagmaE677.e255_characterizations {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x : α) :
    (x = op (op (op x x) x) x ↔ ∃ y : α, op y x = x) ∧
    ((∃ y : α, op y x = x) ↔ ∃ w : α, op (op x w) x = x) ∧
    ((∃ w : α, op (op x w) x = x) ↔ ∃ z : α, op x (op z x) = z) ∧
    ((∃ z : α, op x (op z x) = z) ↔ ∃ y : α, op (op x y) x = y) ∧
    ((∃ y : α, op (op x y) x = y) ↔ ∃ y : α, op x (op y y) = y) := by sorry
