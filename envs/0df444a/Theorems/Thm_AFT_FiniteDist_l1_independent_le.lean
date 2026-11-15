-- Prove2me | Theorems.Thm_AFT_FiniteDist_l1_independent_le
-- name    : AFT.FiniteDist.l1_independent_le
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T09:33:45.82607+00:00
-- url     : https://prove2.me/theorems/e92c7c06-778a-4af3-a7de-58a804e1f052
-- title:
--   L1 distance between independent distributions on a finite index set
-- statement:
--   For any finite index type and finite state type, let two families of probability distributions be indexed by that index type. The L1 distance between their independent joint distributions is at most the sum over indices of the L1 distances between corresponding marginals. This includes an empty index set.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/FiniteIndependentSampling.lean, lines 57–73; exact native theorem type and complete proof.

import Definitions.Def_InfoLossLAR_Native_AFT_FiniteConcentration
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.joint
end AFT.FiniteDist.joint
section



/-! # Product samplers with coordinate-dependent output alphabets -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

 

 

 

 

 set_option maxRecDepth 8192

theorem _root_.AFT.FiniteDist.l1_independent_le {Index State : Type*} [Fintype Index] [DecidableEq Index] [Fintype State]
    (first second : Index → FiniteDist State) :
    (∑ word,|(independent first).weight word-(independent second).weight word|)≤
      ∑ i,∑ point,|(first i).weight point-(second i).weight point| := by sorry
