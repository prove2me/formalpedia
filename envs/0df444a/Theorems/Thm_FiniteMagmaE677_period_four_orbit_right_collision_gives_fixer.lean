-- Prove2me | Theorems.Thm_FiniteMagmaE677_period_four_orbit_right_collision_gives_fixer
-- name    : FiniteMagmaE677.period_four_orbit_right_collision_gives_fixer
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-23T20:38:42.855971+00:00
-- url     : https://prove2.me/theorems/2eb85426-afc2-4ff3-a733-2af7c55e0033
-- title:
--   D4.3 — Period-four collision gives a fixer
-- statement:
--   **CONJECTURED — period-four orbit-collision closeout.** Let a finite magma satisfy E677. Suppose the left orbit of $x$ has exact period four, displayed as
--
--   $$x\longmapsto c_1\longmapsto c_2\longmapsto c_3\longmapsto x,$$
--
--   where $x$ differs from $c_1,c_2,c_3$. For distinct elements $a,b$ on this left orbit, assume
--
--   $$a\diamond x=b\diamond x.$$
--
--   The target is
--
--   $$\exists y,\quad y\diamond x=x.$$
--
--   This specializes the mission's arbitrary-period orbit-collision target. The proved first-return reduction gives five tagged cycle branches; their fixer closeouts remain open. A checked reduction records how this target depends on those branches without asserting that any branch is solved. The statement covers every finite carrier size, but only base points whose left orbit has exact period four.
-- source:
--   Adam McKenna, The Missing Pair, revision 9b76827c2246f0e6288466768f15b5c6f9350d71; lean/E677/Spine/Piece1D4CycleContact.lean, E677D4QCycleContactBranch and e677_d4_q_cycleContactPacket_of_firstReturnPacket; docs/current/e677-closure-plan-2026-08-04.md, D4 first-return collapse frontier. https://github.com/flound1129/the-missing-pair/blob/9b76827c2246f0e6288466768f15b5c6f9350d71/lean/E677/Spine/Piece1D4CycleContact.lean

import Definitions.Def_FiniteMagmaE677_d4_first_return

universe u

open FiniteMagmaE677.FirstReturn

theorem FiniteMagmaE677.period_four_orbit_right_collision_gives_fixer
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x c1 c2 c3 : α)
    (hc1 : op x x = c1)
    (hc2 : op x c1 = c2)
    (hc3 : op x c2 = c3)
    (hcloses : op x c3 = x)
    (hx_ne_c1 : x ≠ c1)
    (hx_ne_c2 : x ≠ c2)
    (hx_ne_c3 : x ≠ c3)
    (a b : α)
    (ha : FiniteMagmaE677.InLeftOrbit op x a)
    (hb : FiniteMagmaE677.InLeftOrbit op x b)
    (hab : a ≠ b)
    (hcollision : op a x = op b x)
    : FiniteMagmaE677.HasFixerAt op x := by sorry
