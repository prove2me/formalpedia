-- Prove2me | solution 1 for mme_cyclicSymmetrization_kronPow_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T05:03:08.704062+00:00
-- url     : https://prove2.me/submissions/c093534d-d267-4087-96e9-2b7f5bfd45ce

import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_permutation
import Definitions.Def_mme_rank_bridge

open MME

universe u

namespace CWCyclicSymmetrizationKronPowIso

theorem permuteModes_eq_permObj
    {K : Type u} [Field K]
    (e : Equiv.Perm (Fin 3)) (X : TensorObj K 3) :
    permuteModes e X = TensorObj.permObj e X := by
  rfl

theorem toQ_permuteModes_kronPow
    {K : Type u} [Field K]
    (e : Equiv.Perm (Fin 3)) (X : TensorObj K 3) (n : ℕ) :
    TensorQ.toQ (permuteModes e (X.kronPow n)) =
      (TensorQ.toQ (permuteModes e X)) ^ n := by
  rw [permuteModes_eq_permObj, permuteModes_eq_permObj]
  change TensorQ.permAut e (TensorQ.toQ (X.kronPow n)) =
    (TensorQ.permAut e (TensorQ.toQ X)) ^ n
  rw [TensorQ.toQ_kronPow, map_pow]

end CWCyclicSymmetrizationKronPowIso

theorem solution
    {K : Type u} [Field K]
    (X : TensorObj K 3) (n : ℕ) :
    TensorObj.Isomorphic
      ((cyclicSymmetrization X).kronPow n)
      (cyclicSymmetrization (X.kronPow n)) := by
  apply TensorQ.toQ_eq_iff.mp
  unfold cyclicSymmetrization
  simp only [TensorQ.toQ_kronPow, TensorQ.toQ_kron]
  rw [CWCyclicSymmetrizationKronPowIso.toQ_permuteModes_kronPow,
    CWCyclicSymmetrizationKronPowIso.toQ_permuteModes_kronPow]
  simp only [mul_pow]
