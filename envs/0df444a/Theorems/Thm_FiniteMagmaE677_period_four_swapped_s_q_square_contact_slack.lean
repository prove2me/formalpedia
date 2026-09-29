-- Prove2me | Theorems.Thm_FiniteMagmaE677_period_four_swapped_s_q_square_contact_slack
-- name    : FiniteMagmaE677.period_four_swapped_s_q_square_contact_slack
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-24T08:36:23.277947+00:00
-- url     : https://prove2.me/theorems/15593718-1d62-4e63-8c2b-75f2d8c64ac1
-- title:
--   D4.4e: q-square contact slack
-- statement:
--   Write $L_x(y)=x\diamond y$ and let $C_z=\{L_x^i(z):0\le i<d_z\}$ for an exact first-return cycle of length $d_z$. Let a magma have decidable equality, exact first-return cycles $C_t,C_p$, and q-square seed data for $p,u$. Put $v=q\diamond q$ and suppose $v\in C_t\cup C_p$. For a finite set of marked points $M$, define $\sigma(M)=|(C_t\cup C_p)\setminus M|$.
--
--   Then
--   $$\sigma(\{p,u,v\})+1=\sigma(\{p,u\}).$$
--
--   The q-square seed supplies $v\ne p,u$, so this contact removes exactly one previously unmarked point. The statement is local to these fixed cycles and does not provide a recursive descent argument.
-- source:
--   https://github.com/flound1129/the-missing-pair/blob/f9945b937be61f4ca48eb6cafdcfa07ba7a7f78c/lean/E677/Spine/Piece1D4SSwapPNewQSquareRenewal.lean#L224

import Definitions.Def_FiniteMagmaE677_sswap_renewal
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.period_four_swapped_s_q_square_contact_slack
{α : Type u} [DecidableEq α] (op : α → α → α)
(x c1 c2 c3 q s t p u : α)
(first : FirstReturn.D4FirstReturn op x c1 c2 c3 t 0)
(pFirst : FirstReturn.D4FirstReturn op x c1 c2 c3 p 0)
(seed : SSwap.QSquareSeed op x c1 c2 c3 q s p u)
(on_accounted : op q q ∈
  SSwap.cyclePoints op x t first.period ∪ SSwap.cyclePoints op x p pFirst.period) :
SSwap.markedSlack op x t p first.period pFirst.period {p, u, op q q} + 1 =
  SSwap.markedSlack op x t p first.period pFirst.period {p, u} := by sorry
