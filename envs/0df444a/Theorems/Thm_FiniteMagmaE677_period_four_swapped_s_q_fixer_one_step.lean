-- Prove2me | Theorems.Thm_FiniteMagmaE677_period_four_swapped_s_q_fixer_one_step
-- name    : FiniteMagmaE677.period_four_swapped_s_q_fixer_one_step
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-24T08:35:37.136405+00:00
-- url     : https://prove2.me/theorems/b006df71-0771-437c-a546-e36f8834ec36
-- title:
--   D4.4b: one-step q-seed pump
-- statement:
--   Write $L_x(y)=x\diamond y$ and let $C_z=\{L_x^i(z):0\le i<d_z\}$ for an exact first-return cycle of length $d_z$. Let a finite magma satisfy E677, with an exact first-return cycle at $t$ and the swapped-S cycle-renewal packet. Assume $q=c_2\diamond x$ and $s=c_3\diamond q$. Put $p=q\diamond(q\diamond x)$ and $u=q\diamond p$.
--
--   There is a one-step packet retaining the renewal input and canonical q/s equations. It records freshness of both $p,u$ outside the six named points, $u\ne p$, $p\diamond q=q$, $q\diamond u=q$, and $u\diamond q\ne q$, together with all five cycle-location alternatives:
--
--   1. Both $p,u$ lie on $C_t$, at distinct phases.
--   2. $p$ lies on $C_t$ and $u$ starts a disjoint cycle.
--   3. $p$ starts a new cycle and $u$ lies on $C_t$.
--   4. $p$ starts a new cycle and $u$ lies at a strictly positive phase of $C_p$.
--   5. $p$ starts a new cycle and $u$ starts a cycle disjoint from both $C_t,C_p$.
--
--   Contact phases carry their exact equations and bounds; escaping seeds carry exact first-return data. This asserts one step, without an iteration or termination conclusion.
-- source:
--   https://github.com/flound1129/the-missing-pair/blob/f9945b937be61f4ca48eb6cafdcfa07ba7a7f78c/lean/E677/Spine/Piece1D4SSwapQFixerPump.lean#L87

import Definitions.Def_FiniteMagmaE677_sswap_renewal
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.period_four_swapped_s_q_fixer_one_step
{α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(x c1 c2 c3 q s t : α)
(first : FirstReturn.D4FirstReturn op x c1 c2 c3 t 0)
(input : SSwap.CycleRenewal op x c1 c2 c3 q s t first)
(q_eq : q = op c2 x) (s_eq : s = op c3 q) :
SSwap.Pump op x c1 c2 c3 q s t (op q (op q x)) (op q (op q (op q x))) first := by sorry
