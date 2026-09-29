-- Prove2me | Theorems.Thm_FiniteMagmaE677_e677_orbit_collision_reduces_to_crux
-- name    : FiniteMagmaE677.e677_orbit_collision_reduces_to_crux
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-23T20:58:42.6673+00:00
-- url     : https://prove2.me/theorems/e8bb19fb-7614-4f5c-b2df-a3bf37dd3263
-- title:
--   General orbit collision reduces to the self-product crux
-- statement:
--   Reduction of a general (m,n) right-collision on the left orbit of x to the (0,1)-crux. Given E677, x, and m n with op (L_x^m x) x = op (L_x^n x) x, either the colliding elements coincide, or the collision shifts down to the self-product case op (op x x) x = op x x, or x admits a fixer. Combined with the crux node -- which closes the self-product case to op x x = x, collapsing the whole left orbit of x to x -- this yields the parent principle OrbitRightCollisionOrFixer.
-- source:
--   Decomposition of FiniteMagmaE677.orbit_right_collision_or_fixer (02499794-6499-4013-bc56-42ca08b0e071), Equational Magmas E677->E255 mission; attack plan in p2m_harness/eqmagmas_triage.md

import Definitions.Def_FiniteMagmaE677

set_option autoImplicit false

universe u

theorem FiniteMagmaE677.e677_orbit_collision_reduces_to_crux {α : Type u} [Fintype α]
    (op : α → α → α) (h677 : FiniteMagmaE677.E677 op) (x : α)
    (m n : ℕ)
    (hcoll : op ((op x)^[m] x) x = op ((op x)^[n] x) x) :
    (op x)^[m] x = (op x)^[n] x ∨ op (op x x) x = op x x ∨ FiniteMagmaE677.HasFixerAt op x := by sorry
