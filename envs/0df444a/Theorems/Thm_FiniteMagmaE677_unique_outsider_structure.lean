-- Prove2me | Theorems.Thm_FiniteMagmaE677_unique_outsider_structure
-- name    : FiniteMagmaE677.unique_outsider_structure
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T08:02:49.032979+00:00
-- url     : https://prove2.me/theorems/d446f5a1-8aec-4538-9229-032c8f4591e3
-- title:
--   Structural facts about the unique element outside a left orbit
-- statement:
--   Let $x$ be an element of a finite magma satisfying E677, and suppose exactly one element $A$ lies outside the left orbit $O_x = \{L_x^n x\}$. Then:
--
--   1. $A$ is $L_x$-fixed: $x \diamond A = A$;
--   2. the fixer candidate of $A$ is $x$: $(A \diamond A) \diamond A = x$;
--   3. $A$ is not idempotent: $A \diamond A \neq A$;
--   4. $A \diamond (A \diamond x) = A$;
--   5. $A \diamond x$ lies on the orbit: $A \diamond x \neq A$ and $A \diamond x \in O_x$;
--   6. $x \neq A$.
--
--   These are the opening derivations of the accepted reduction `unique_left_orbit_complement_collision_gives_fixer`, extracted as importable facts: under the singleton-complement hypothesis, the outsider is $L_x$-fixed, its fixer candidate is $x$ itself, and its right translate by $x$ returns to the orbit.
-- source:
--   Opening derivations of the accepted sketch 139884f7 on the Prove2Me mission 'Equational Magmas: E677 → E255 (finite case)', matching zjay5's structural analysis of 2026-09-22; formalized here.

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_fixer_unique

universe u

theorem FiniteMagmaE677.unique_outsider_structure {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x A : α)
    (hA_notin : ¬ FiniteMagmaE677.InLeftOrbit op x A)
    (hA_unique : ∀ a : α, ¬ FiniteMagmaE677.InLeftOrbit op x a → a = A) :
    op x A = A ∧
    op (op A A) A = x ∧
    op A A ≠ A ∧
    op A (op A x) = A ∧
    FiniteMagmaE677.InLeftOrbit op x (op A x) ∧
    x ≠ A := by sorry
