-- Prove2me | solution 1 for tvDistance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:26.273077+00:00
-- url     : https://prove2.me/submissions/8b663e55-161d-476a-a6fb-5b28d2eb1146

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
    0 ≤ tvDistance μ ν :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
