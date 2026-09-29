-- Prove2me | Theorems.Thm_FiniteMagmaE677_e677_self_product_collision_crux
-- name    : FiniteMagmaE677.e677_self_product_collision_crux
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-23T20:58:46.055597+00:00
-- url     : https://prove2.me/theorems/1c6e797c-612e-40e2-8068-adf0f0cf4d21
-- title:
--   Self-product right collision forces idempotence: the (0,1)-crux
-- statement:
--   The (0,1)-crux of the orbit-collision principle (Piece 1 of the E677->E255 finite mission). Let A be finite with a binary operation op satisfying E677, fix x in A, and put s := op x x. Suppose op s x = s. By Lemma 13.1(ii) every fixer y of x equals op (op x x) x, hence equals op s x = s; a fixer satisfies op y x = x, i.e. op s x = x, and with the crux hypothesis this forces s = x -- so the fixer disjunct is redundant and the whole claim is op s x = s -> s = x. From E677(x,x) we get x = L_x^3 x, and with L_x injective the left orbit of x is a cycle of length in {1,2,3}: length 1 is the goal s = x; length 2 is ruled out (x = op x (op x s) = op x x = s contradicts s != x); length 3 -- with C = {x,s,t} and the partial constraints op t s = s, op t x = t, op s t = x -- is the explicit remaining obligation.
-- source:
--   Decomposition of FiniteMagmaE677.orbit_right_collision_or_fixer (02499794-6499-4013-bc56-42ca08b0e071), Equational Magmas E677->E255 mission; attack plan in p2m_harness/eqmagmas_triage.md

import Definitions.Def_FiniteMagmaE677

set_option autoImplicit false

universe u

theorem FiniteMagmaE677.e677_self_product_collision_crux {α : Type u} [Fintype α]
    (op : α → α → α) (h677 : FiniteMagmaE677.E677 op) (x : α)
    (hinj : Function.Injective (op x))
    (h3 : (op x)^[3] x = x)
    (hcoll : op (op x x) x = op x x) :
    op x x = x := by sorry
