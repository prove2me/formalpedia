-- Prove2me | solution 1 for mme_sixSymmetrization_kronPow_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:03:14.458823+00:00
-- url     : https://prove2.me/submissions/35a153b0-0cf2-4b1c-96d0-8eff92397a69

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_cyclicSymmetrization_kronPow_isomorphic

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (T : TensorObj K 3) (n : ℕ) :
    TensorObj.Isomorphic
      ((sixSymmetrization T).kronPow n)
      (sixSymmetrization (T.kronPow n)) := by
  apply (TensorQ.toQ_eq_iff).1
  rw [TensorQ.toQ_kronPow]
  change
    (TensorQ.toQ (cyclicSymmetrization T) *
        TensorQ.permAut swapFirstTwoPerm
          (TensorQ.toQ (cyclicSymmetrization T))) ^ n =
      TensorQ.toQ (cyclicSymmetrization (T.kronPow n)) *
        TensorQ.permAut swapFirstTwoPerm
          (TensorQ.toQ (cyclicSymmetrization (T.kronPow n)))
  have hcyclic :
      TensorQ.toQ (cyclicSymmetrization (T.kronPow n)) =
        (TensorQ.toQ (cyclicSymmetrization T)) ^ n := by
    rw [← TensorQ.toQ_kronPow]
    exact (TensorQ.toQ_eq_iff).2
      (mme_cyclicSymmetrization_kronPow_isomorphic T n).symm
  rw [hcyclic, map_pow, mul_pow]
