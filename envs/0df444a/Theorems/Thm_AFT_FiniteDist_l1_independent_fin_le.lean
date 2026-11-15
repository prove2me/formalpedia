-- Prove2me | Theorems.Thm_AFT_FiniteDist_l1_independent_fin_le
-- name    : AFT.FiniteDist.l1_independent_fin_le
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T06:15:45.072355+00:00
-- url     : https://prove2.me/theorems/5b1e9356-a76d-4f92-96f9-84074dbe336a
-- title:
--   L1 distance bound for finite independent product distributions
-- statement:
--   Let A be any finite type and let two families of probability distributions on A be indexed by Fin count, for an arbitrary natural count. The L1 distance between their independent joint distributions is at most the sum, over all coordinates, of the L1 distances between the corresponding marginal distributions. This also includes the empty product.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/FiniteProductVariation.lean, lines 45–64; exact native theorem type and complete proof.

import Definitions.Def_InfoLossLAR_Native_AFT_FiniteConcentration
import Mathlib
section


/-! # Total variation of actual independent finite products -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [Fintype A] [Fintype B]





set_option maxRecDepth 8192

omit [Fintype B] in

theorem _root_.AFT.FiniteDist.l1_independent_fin_le (count : ℕ) (first second : Fin count → _root_.AFT.FiniteDist A) :
    (∑ word,|(_root_.AFT.FiniteDist.independent first).weight word-(_root_.AFT.FiniteDist.independent second).weight word|) ≤
      ∑ i,∑ a,|(first i).weight a-(second i).weight a| := by sorry
