-- Prove2me | Theorems.Thm_FiniteMagmaE677_period_four_swapped_s_q_square_refinement
-- name    : FiniteMagmaE677.period_four_swapped_s_q_square_refinement
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-24T08:35:57.626841+00:00
-- url     : https://prove2.me/theorems/b5ea7171-e05c-41b3-934b-a4026a5ce47a
-- title:
--   D4.4c: q-square refinement
-- statement:
--   Write $L_x(y)=x\diamond y$ and let $C_z=\{L_x^i(z):0\le i<d_z\}$ for an exact first-return cycle of length $d_z$. Let a finite magma satisfy E677 and carry the swapped-S one-step packet with $p=q\diamond(q\diamond x)$ and $u=q\diamond p$. Put $v=q\diamond q$.
--
--   Then $v$ is outside the six named points, $v\ne p$, $v\ne u$, and $p=u\diamond v$. Moreover, the full five-way one-step classification admits the following refinement, preserving each original packet and branch payload. If both $p,u$ lie on $C_t$, either $v$ occupies a third distinct phase there with the oriented phase-product identity, or $v$ starts a disjoint cycle. If $p$ starts a new cycle and $u$ lies on $C_t$ or $C_p$, then $v$ lies on $C_t$, lies on $C_p$, or starts a cycle disjoint from both. Every contact keeps the identity $p=u\diamond v$ in its corresponding ordered phase form; phases on $C_p$ are strictly positive, and same-cycle phases of $u,v$ are distinct. The two branches in which $u$ escapes retain their original full payloads.
--
--   The conclusion supplies both the q-square seed facts and this complete refined outcome. It does not establish recursive renewal or a fixer at $x$.
-- source:
--   https://github.com/flound1129/the-missing-pair/blob/f9945b937be61f4ca48eb6cafdcfa07ba7a7f78c/lean/E677/Spine/Piece1D4SSwapQSquareRenewal.lean#L35 and https://github.com/flound1129/the-missing-pair/blob/f9945b937be61f4ca48eb6cafdcfa07ba7a7f78c/lean/E677/Spine/Piece1D4SSwapPNewQSquareRenewal.lean#L377

import Definitions.Def_FiniteMagmaE677_sswap_renewal
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.period_four_swapped_s_q_square_refinement
{α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(x c1 c2 c3 q s t : α)
(first : FirstReturn.D4FirstReturn op x c1 c2 c3 t 0)
(pump : SSwap.Pump op x c1 c2 c3 q s t
  (op q (op q x)) (op q (op q (op q x))) first) :
SSwap.QSquareSeed op x c1 c2 c3 q s (op q (op q x)) (op q (op q (op q x))) ∧
SSwap.QSquareOutcome op x c1 c2 c3 q s t
  (op q (op q x)) (op q (op q (op q x))) first := by sorry
