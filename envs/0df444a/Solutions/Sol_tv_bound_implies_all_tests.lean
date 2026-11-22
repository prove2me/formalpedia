-- Prove2me | solution 1 for tv_bound_implies_all_tests
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:46.671403+00:00
-- url     : https://prove2.me/submissions/61481e17-eb8b-407b-a1d7-cc8e2ee85024

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
public import Theorems.Thm_expectation_approx_of_tv

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution {H : Type*} [Fintype H]
    (μ ν : FinitePMF H) (ε : ℝ)
    (hε : tvDistance μ ν ≤ ε)
    (tests : Finset (H → Bool)) :
    ∀ f ∈ tests, |boolTestExpectation μ f - boolTestExpectation ν f| ≤ ε :=
  fun f _ => expectation_approx_of_tv μ ν f ε hε
