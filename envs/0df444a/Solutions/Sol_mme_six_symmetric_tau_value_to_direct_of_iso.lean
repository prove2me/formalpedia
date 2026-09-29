-- Prove2me | solution 1 for mme_six_symmetric_tau_value_to_direct_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T09:39:23.950831+00:00
-- url     : https://prove2.me/submissions/2d491e39-da82-4ab8-b348-614aa554a670

import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

open MME

universe u

theorem solution
    {K : Type u} [Field K]
    (T : TensorObj K 3) (tau V : ℝ) (hV : 0 ≤ V)
    (hsym : TensorObj.Isomorphic
      (sixSymmetrization T) (T.kronPow 6))
    (h : HasSixSymmetricTauValueAtLeast T tau V) :
    HasTauValueAtLeast T tau V := by
  apply mme_HasTauValueAtLeast_kronPow_root T tau V 6 (by norm_num) hV
  exact mme_HasTauValueAtLeast_mono_restrict hsym.1 h
