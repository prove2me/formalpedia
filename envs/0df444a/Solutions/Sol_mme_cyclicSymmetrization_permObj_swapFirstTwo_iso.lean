-- Prove2me | solution 1 for mme_cyclicSymmetrization_permObj_swapFirstTwo_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:56:57.800371+00:00
-- url     : https://prove2.me/submissions/735e1cad-b8af-4fdd-8900-ffb60171e159

import Mathlib.Tactic
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_six_symmetrized_tau_value

open MME

universe u

set_option autoImplicit false

namespace CyclicSwapNaturalitySolution

private theorem permObj_trans_iso
    {K : Type u} [Field K] {d : ℕ}
    (e e' : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.permObj e' (TensorObj.permObj e X))
      (TensorObj.permObj (e.trans e') X) := by
  have ht : (TensorObj.permObj e' (TensorObj.permObj e X)).t =
      (TensorObj.permObj (e.trans e') X).t := by
    exact PiTensorProduct.reindex_reindex e e' X.t
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (TensorObj.permObj (e.trans e') X).V))
      (TensorObj.permObj (e.trans e') X).t
    exact hmap.trans ht.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (TensorObj.permObj e' (TensorObj.permObj e X)).V))
      (TensorObj.permObj e' (TensorObj.permObj e X)).t
    exact hmap.trans ht

private theorem swap_trans_cyclic :
    swapFirstTwoPerm.trans cyclicPerm =
      (cyclicPerm.trans cyclicPerm).trans swapFirstTwoPerm := by
  ext i
  fin_cases i <;> rfl

private theorem swap_trans_cyclic_sq :
    swapFirstTwoPerm.trans (cyclicPerm.trans cyclicPerm) =
      cyclicPerm.trans swapFirstTwoPerm := by
  ext i
  fin_cases i <;> rfl

end CyclicSwapNaturalitySolution

theorem solution
    {K : Type u} [Field K] (X : TensorObj K 3) :
    TensorObj.Isomorphic
      (cyclicSymmetrization (TensorObj.permObj swapFirstTwoPerm X))
      (TensorObj.permObj swapFirstTwoPerm (cyclicSymmetrization X)) := by
  apply (TensorQ.toQ_eq_iff).1
  rw [cyclicSymmetrization_eq_public_perm,
    cyclicSymmetrization_eq_public_perm]
  simp only [TensorQ.toQ_kron, ← TensorQ.permAut_toQ, map_mul]
  have h1 :
      TensorQ.toQ
          (TensorObj.permObj cyclicPerm
            (TensorObj.permObj swapFirstTwoPerm X)) =
        TensorQ.toQ
          (TensorObj.permObj swapFirstTwoPerm
            (TensorObj.permObj (cyclicPerm.trans cyclicPerm) X)) := by
    apply (TensorQ.toQ_eq_iff).2
    exact
      (CyclicSwapNaturalitySolution.permObj_trans_iso
          swapFirstTwoPerm cyclicPerm X).trans
        ((by
          simpa only [CyclicSwapNaturalitySolution.swap_trans_cyclic] using
            (CyclicSwapNaturalitySolution.permObj_trans_iso
              (cyclicPerm.trans cyclicPerm)
              swapFirstTwoPerm X).symm) :
          TensorObj.Isomorphic
            (TensorObj.permObj (swapFirstTwoPerm.trans cyclicPerm) X)
            (TensorObj.permObj swapFirstTwoPerm
              (TensorObj.permObj
                (cyclicPerm.trans cyclicPerm) X)))
  have h2 :
      TensorQ.toQ
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (TensorObj.permObj swapFirstTwoPerm X)) =
        TensorQ.toQ
          (TensorObj.permObj swapFirstTwoPerm
            (TensorObj.permObj cyclicPerm X)) := by
    apply (TensorQ.toQ_eq_iff).2
    exact
      (CyclicSwapNaturalitySolution.permObj_trans_iso swapFirstTwoPerm
          (cyclicPerm.trans cyclicPerm) X).trans
        ((by
          simpa only [CyclicSwapNaturalitySolution.swap_trans_cyclic_sq] using
            (CyclicSwapNaturalitySolution.permObj_trans_iso
              cyclicPerm swapFirstTwoPerm X).symm) :
          TensorObj.Isomorphic
            (TensorObj.permObj
              (swapFirstTwoPerm.trans (cyclicPerm.trans cyclicPerm)) X)
            (TensorObj.permObj swapFirstTwoPerm
              (TensorObj.permObj cyclicPerm X)))
  change
    TensorQ.toQ (TensorObj.permObj swapFirstTwoPerm X) *
        (TensorQ.toQ
            (TensorObj.permObj cyclicPerm
              (TensorObj.permObj swapFirstTwoPerm X)) *
          TensorQ.toQ
            (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
              (TensorObj.permObj swapFirstTwoPerm X))) =
      TensorQ.toQ (TensorObj.permObj swapFirstTwoPerm X) *
        (TensorQ.toQ
            (TensorObj.permObj swapFirstTwoPerm
              (TensorObj.permObj cyclicPerm X)) *
          TensorQ.toQ
            (TensorObj.permObj swapFirstTwoPerm
              (TensorObj.permObj (cyclicPerm.trans cyclicPerm) X)))
  rw [h1, h2]
  ac_rfl
