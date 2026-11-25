-- Prove2me | solution 1 for isCompact_convexWeights
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:01.125309+00:00
-- url     : https://prove2.me/submissions/66b9c795-39bf-4eee-9f7f-4476ab67b088

module
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Definitions.Def_BasicResults_CompactConvexHull

set_option autoImplicit true
@[expose] public section
public section
theorem _root_.solution (k : ℕ) :
    IsCompact {w : Fin k → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
  refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    ?_ fun w hw i _ => ⟨hw.1 i, ?_⟩
  · rw [Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le
      (continuous_const : Continuous fun _ : Fin k → ℝ => (0 : ℝ)) (continuous_apply i)).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  · rw [← hw.2]
    exact Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)
