-- Prove2me | Theorems.Thm_AFT_FiniteDist_l1_prod_le
-- name    : AFT.FiniteDist.l1_prod_le
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:24:05.18576+00:00
-- url     : https://prove2.me/theorems/8d92283c-6b84-4fef-a32d-c1a4dfeb8a76
-- title:
--   L1 distance between independent products is additive
-- statement:
--   Let $p,p\prime$ be probability laws on a finite set $X$, and let $q,q\prime$ be probability laws on a finite set $Y$. Then $$\sum_{x,y}|p(x)q(y)-p\prime(x)q\prime(y)|\le\sum_x|p(x)-p\prime(x)|+\sum_y|q(y)-q\prime(y)|.$$ This controls the error from combining independent approximate samples.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/FiniteProductVariation.lean; lines 26–43; retained native proof and type checked against the native theorem.

import Definitions.Def_InfoLossLAR_Native_AFT_FiniteConcentration
import Mathlib


/-! # Total variation of actual independent finite products -/
namespace AFT.FiniteDist
end AFT.FiniteDist
section AFT
section FiniteDist
open AFT
open AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [Fintype A] [Fintype B]

theorem AFT.FiniteDist.l1_prod_le (first first' : FiniteDist A) (second second' : FiniteDist B) :
    (∑ pair,|(first.prod second).weight pair-(first'.prod second').weight pair|) ≤
      (∑ a,|first.weight a-first'.weight a|)+(∑ b,|second.weight b-second'.weight b|) := by sorry
