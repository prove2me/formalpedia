-- Prove2me | Theorems.Thm_FiniteMagmaE677_period_four_swapped_s_q_square_growth_cardinality
-- name    : FiniteMagmaE677.period_four_swapped_s_q_square_growth_cardinality
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-24T08:36:03.047349+00:00
-- url     : https://prove2.me/theorems/37549276-f0b5-447f-8264-eaaa14432030
-- title:
--   D4.4d: q-square strict-growth cardinality
-- statement:
--   Write $L_x(y)=x\diamond y$ and let $C_z=\{L_x^i(z):0\le i<d_z\}$ for an exact first-return cycle of length $d_z$. Let a magma have decidable equality and carry a swapped-S one-step packet at $x,c_1,c_2,c_3,q,s,t,p,u$. Assume $p$ is off $C_t$ and has exact first-return cycle $C_p$. Put $v=q\diamond q$; assume $v$ is outside the six named points, off both $C_t,C_p$, and has exact first-return cycle $C_v$.
--
--   Then the accounted union has exact size
--   $$\left|\{x,c_1,c_2,c_3,q,s\}\cup C_t\cup C_p\cup C_v\right|=6+d_t+d_p+d_v.$$
--
--   This is a conditional finite-set count. The packet and cycle hypotheses suffice; no ambient finiteness or separate E677 hypothesis is required.
-- source:
--   https://github.com/flound1129/the-missing-pair/blob/f9945b937be61f4ca48eb6cafdcfa07ba7a7f78c/lean/E677/Spine/Piece1D4SSwapPNewQSquareRenewal.lean#L282

import Definitions.Def_FiniteMagmaE677_sswap_renewal
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.period_four_swapped_s_q_square_growth_cardinality
{α : Type u} [DecidableEq α] (op : α → α → α)
(x c1 c2 c3 q s t p u : α)
(first : FirstReturn.D4FirstReturn op x c1 c2 c3 t 0)
(pump : SSwap.Pump op x c1 c2 c3 q s t p u first)
(p_off_t : ∀ k, k < first.period → p ≠ (op x)^[k] t)
(pFirst : FirstReturn.D4FirstReturn op x c1 c2 c3 p 0)
(fresh : FirstReturn.FreshOutsideSix x c1 c2 c3 q s (op q q))
(v_off_t : ∀ k, k < first.period → op q q ≠ (op x)^[k] t)
(v_off_p : ∀ k, k < pFirst.period → op q q ≠ (op x)^[k] p)
(vFirst : FirstReturn.D4FirstReturn op x c1 c2 c3 (op q q) 0) :
(((SSwap.namedSix x c1 c2 c3 q s ∪ SSwap.cyclePoints op x t first.period) ∪
    SSwap.cyclePoints op x p pFirst.period) ∪
    SSwap.cyclePoints op x (op q q) vFirst.period).card =
  6 + first.period + pFirst.period + vFirst.period := by sorry
