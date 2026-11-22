-- Prove2me | solution 1 for normalizeToPMF_prob
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:10.590877+00:00
-- url     : https://prove2.me/submissions/749e8140-10b6-4520-8f09-583d2991362f

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution {C : Type*} [Fintype C] [Nonempty C]
    (w : C → ℝ) (hw : ∀ c, 0 < w c) (c : C) :
    (normalizeToPMF w hw).prob c = w c / ∑ c' : C, w c' := rfl
