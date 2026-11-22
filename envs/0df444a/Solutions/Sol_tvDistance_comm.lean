-- Prove2me | solution 1 for tvDistance_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:26.745227+00:00
-- url     : https://prove2.me/submissions/91aa4694-bf85-422e-aba4-fb3a0b854891

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution {H : Type*} [Fintype H]
    (μ ν : FinitePMF H) :
    tvDistance μ ν = tvDistance ν μ := by
  simp only [tvDistance, abs_sub_comm]
