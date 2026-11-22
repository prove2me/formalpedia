-- Prove2me | solution 1 for mwuInit_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:32:44.215259+00:00
-- url     : https://prove2.me/submissions/65eea079-42a8-4411-b9fc-af6ac4308b12

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution (C : Type*) [Fintype C] :
    (mwuInit C).potential = Fintype.card C := by
  simp [MWUConfig.potential, mwuInit, sum_const, nsmul_eq_mul, mul_one]
