-- Prove2me | Theorems.Thm_AFT_FiniteDist_signed_kernel_l1_contraction
-- name    : AFT.FiniteDist.signed_kernel_l1_contraction
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:21:19.227316+00:00
-- url     : https://prove2.me/theorems/a831ea17-49ea-4fa2-9fb7-cc46f3f18f20
-- title:
--   Stochastic kernels contract arbitrary finite signed masses
-- statement:
--   Let $w:X\to\mathbb R$ be any signed mass on a finite set, and let $K(x,\cdot)$ be a probability law on a finite set $Y$ for every $x\in X$. Then $$\sum_{y\in Y}\left|\sum_{x\in X}w(x)K(x,y)\right|\le\sum_{x\in X}|w(x)|.$$ This contraction applies before clipping, without requiring the input mass to be nonnegative or normalized.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/TotalVariation.lean; lines 121–136; retained native proof and type checked against the native theorem.

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

theorem AFT.FiniteDist.signed_kernel_l1_contraction (weight : α → ℝ) (kernel : α → FiniteDist β) :
    (∑ output, |∑ input, weight input * (kernel input).weight output|) ≤
      ∑ input, |weight input| := by sorry
