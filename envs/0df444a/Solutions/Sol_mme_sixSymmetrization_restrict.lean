-- Prove2me | solution 1 for mme_sixSymmetrization_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T07:40:31.36938+00:00
-- url     : https://prove2.me/submissions/6dbfe565-abcf-41cf-a779-cca42f55f1ce

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : TensorObj.Restrict X Y) :
    TensorObj.Restrict (sixSymmetrization X) (sixSymmetrization Y) := by
  have hkron : ∀ {A A' B B' : TensorObj K 3},
      TensorObj.Restrict A A' → TensorObj.Restrict B B' →
      TensorObj.Restrict (TensorObj.kron A B) (TensorObj.kron A' B') := by
    intro A A' B B' hA hB
    rw [← TensorQ.le_toQ]
    let P := TensorQ.tensorStrassen K 3 (by omega)
    have ha : P.le (TensorQ.toQ A) (TensorQ.toQ A') := hA
    have hb : P.le (TensorQ.toQ B) (TensorQ.toQ B') := hB
    have hleft : P.le
        (TensorQ.toQ A * TensorQ.toQ B)
        (TensorQ.toQ A' * TensorQ.toQ B) :=
      P.mul_right _ _ ha _
    have hright : P.le
        (TensorQ.toQ A' * TensorQ.toQ B)
        (TensorQ.toQ A' * TensorQ.toQ B') := by
      simpa only [mul_comm] using P.mul_right _ _ hb (TensorQ.toQ A')
    exact P.le_trans _ _ _ hleft hright
  have hcyclic : TensorObj.Restrict
      (cyclicSymmetrization X) (cyclicSymmetrization Y) := by
    rw [cyclicSymmetrization_eq_public_perm,
      cyclicSymmetrization_eq_public_perm]
    exact hkron h (hkron
      (TensorObj.permObj_restrict cyclicPerm h)
      (TensorObj.permObj_restrict
        (cyclicPerm.trans cyclicPerm) h))
  unfold sixSymmetrization
  exact hkron hcyclic
    (TensorObj.permObj_restrict swapFirstTwoPerm hcyclic)
