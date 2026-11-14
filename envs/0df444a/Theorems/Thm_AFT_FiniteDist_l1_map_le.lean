-- Prove2me | Theorems.Thm_AFT_FiniteDist_l1_map_le
-- name    : AFT.FiniteDist.l1_map_le
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:24:10.47036+00:00
-- url     : https://prove2.me/theorems/1a4816c0-07ca-4d0e-b749-6b5b4016afae
-- title:
--   Deterministic pushforward contracts finite L1 distance
-- statement:
--   Let $p,q$ be probability laws on a finite set $X$, and let $f:X\to Y$ map into a finite set. Their pushforwards satisfy $$\sum_{y\in Y}|(f_*p)(y)-(f_*q)(y)|\le\sum_{x\in X}|p(x)-q(x)|.$$ Thus deterministic postprocessing cannot increase this distance.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/FiniteProductVariation.lean; lines 10–24; retained native proof and type checked against the native theorem.

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

theorem AFT.FiniteDist.l1_map_le (first second : FiniteDist A) (map : A → B) :
    (∑ b,|(first.map map).weight b-(second.map map).weight b|) ≤ ∑ a,|first.weight a-second.weight a| := by sorry
