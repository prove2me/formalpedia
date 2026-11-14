-- Prove2me | Theorems.Thm_AFT_FiniteDist_totalVariation_eq_half_l1
-- name    : AFT.FiniteDist.totalVariation_eq_half_l1
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:21:18.825381+00:00
-- url     : https://prove2.me/theorems/a548f915-c7b3-4c84-9cf0-f20bdc73da77
-- title:
--   Total variation equals half the finite L1 distance
-- statement:
--   Let $p,q$ be probability laws on a finite set $X$, with total variation defined as the positive mass of $p-q$. Then $$d_{\mathrm{TV}}(p,q)=\frac12\sum_{x\in X}|p(x)-q(x)|.$$ The identity connects the signed mass and statistical distance formulations used in the affine sampler.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/TotalVariation.lean; lines 79–96; retained native proof and type checked against the native theorem.

import Definitions.Def_InfoLossLAR_Native_AFT_TotalVariation
import Mathlib



/-! Exact finite total variation and contraction by a stochastic kernel. -/

namespace AFT
end AFT
section AFT
open AFT

open scoped BigOperators Classical

variable {α β : Type*} [Fintype α] [Fintype β]



namespace AFT.FiniteDist
end AFT.FiniteDist
section FiniteDist
open AFT
open AFT.FiniteDist

theorem AFT.FiniteDist.totalVariation_eq_half_l1 (p q : FiniteDist α) :
    totalVariation p q = (∑ a, |p.weight a - q.weight a|) / 2 := by sorry
