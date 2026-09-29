-- Prove2me | Theorems.Thm_FiniteMagmaE677_period_four_swapped_s_gives_cycle_renewal
-- name    : FiniteMagmaE677.period_four_swapped_s_gives_cycle_renewal
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-24T08:35:34.02099+00:00
-- url     : https://prove2.me/theorems/117c5de0-edf3-465f-ae9f-1754dca680b3
-- title:
--   D4.4a: swapped-S cycle renewal
-- statement:
--   Write $L_x(y)=x\diamond y$ and let $C_z=\{L_x^i(z):0\le i<d_z\}$ for an exact first-return cycle of length $d_z$. Let a finite magma satisfy E677. Assume the published distinguished period-four packet and S-tagged start at $x,c_1,c_2,c_3$. Put $q=c_2\diamond x$, $s=c_3\diamond q$ and $t=c_2\diamond s$. Suppose $L_x(q)=s$, $L_x(s)=q$, $t$ is outside $\{x,c_1,c_2,c_3,q,s\}$, the trace at $t$ is initialized at depth zero with exact first-return data, and $t\diamond c_2=c_3$.
--
--   Then these inputs extend to a cycle-renewal packet. In particular, $(t\diamond c_3)\diamond t=c_1$, $q\diamond c_2=s\diamond c_2$, and $p=q\diamond(q\diamond x)$ is fresh outside the same six points and satisfies $p\diamond q=q$. The packet retains the full three-way classification of $t\diamond c_3$: the dual-collision case, contact at a strictly positive phase of $C_t$, or a fresh cycle disjoint from $C_t$, with the associated equations and exact first-return data.
-- source:
--   https://github.com/flound1129/the-missing-pair/blob/f9945b937be61f4ca48eb6cafdcfa07ba7a7f78c/lean/E677/Spine/Piece1D4SSwapCommonRenewal.lean#L144

import Definitions.Def_FiniteMagmaE677_sswap_renewal
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.period_four_swapped_s_gives_cycle_renewal
{α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(x c1 c2 c3 : α)
(packet : FirstReturn.D4Distinguished op x c1 c2 c3)
(start : FirstReturn.STaggedStart op x c1 c2 c3)
(q_to_s : op x (op c2 x) = op c3 (op c2 x))
(s_to_q : op x (op c3 (op c2 x)) = op c2 x)
(fresh : FirstReturn.FreshOutsideSix x c1 c2 c3
  (op c2 x) (op c3 (op c2 x)) (op c2 (op c3 (op c2 x))))
(initial_trace : FirstReturn.D4Trace op x c1 c2 c3 (op c2 (op c3 (op c2 x))) 0)
(first : FirstReturn.D4FirstReturn op x c1 c2 c3 (op c2 (op c3 (op c2 x))) 0)
(bridge : op (op c2 (op c3 (op c2 x))) c2 = c3) :
SSwap.CycleRenewal op x c1 c2 c3 (op c2 x) (op c3 (op c2 x))
  (op c2 (op c3 (op c2 x))) first := by sorry
