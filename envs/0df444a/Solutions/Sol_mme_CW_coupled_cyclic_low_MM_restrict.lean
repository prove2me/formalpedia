-- Prove2me | solution 1 for mme_CW_coupled_cyclic_low_MM_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:01:42.319525+00:00
-- url     : https://prove2.me/submissions/2a9a15dd-aeb7-49d0-bd81-8cc4ce14ab34

import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_permutation

open MME PiTensorProduct

universe u


namespace CWCoupledCyclicLowMM

theorem cyclic_eq_public
    {K : Type u} [Field K] (X : TensorObj K 3) :
    cyclicSymmetrization X =
      TensorObj.kron X
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm X)
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) X)) := by
  unfold cyclicSymmetrization
  congr 3 <;> apply Equiv.ext <;> intro i <;> fin_cases i <;> rfl

theorem permObj_trans_iso
    {K : Type u} [Field K] {d : ℕ}
    (e e' : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.permObj (e.trans e') X)
      (TensorObj.permObj e' (TensorObj.permObj e X)) := by
  have ht :
      (TensorObj.permObj (e.trans e') X).t =
        (TensorObj.permObj e' (TensorObj.permObj e X)).t := by
    show (PiTensorProduct.reindex K X.V (e.trans e')) X.t =
      (PiTensorProduct.reindex K (fun i => X.V (e.symm i)) e')
        ((PiTensorProduct.reindex K X.V e) X.t)
    exact (PiTensorProduct.reindex_reindex e e' X.t).symm
  refine ⟨⟨fun _ => LinearMap.id, ?_⟩, ⟨fun _ => LinearMap.id, ?_⟩⟩
  · rw [ht]
    exact congrFun (congrArg DFunLike.coe PiTensorProduct.map_id) _
  · rw [← ht]
    exact congrFun (congrArg DFunLike.coe PiTensorProduct.map_id) _

theorem second_cyclic_MM_iso
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 q 1))
      (MMObj K q 1 1) := by
  refine TensorObj.Isomorphic.trans
    (permObj_trans_iso cyclicPerm cyclicPerm (MMObj K 1 q 1)) ?_
  refine TensorObj.Isomorphic.trans
    (TensorObj.permObj_isomorphic cyclicPerm
      (MMObj_permObj_cyclic 1 q 1)) ?_
  exact MMObj_permObj_cyclic 1 1 q

theorem nested_MM_iso
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.kron (MMObj K 1 q 1)
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm (MMObj K 1 q 1))
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (MMObj K 1 q 1))))
      (MMObj K q q q) := by
  have hcyc₁ : TensorObj.Isomorphic
      (TensorObj.permObj cyclicPerm (MMObj K 1 q 1))
      (MMObj K 1 1 q) := MMObj_permObj_cyclic 1 q 1
  have hcyc₂ : TensorObj.Isomorphic
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 q 1))
      (MMObj K q 1 1) := second_cyclic_MM_iso q
  have hblocks : TensorObj.Isomorphic
      (TensorObj.kron (MMObj K 1 q 1)
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm (MMObj K 1 q 1))
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (MMObj K 1 q 1))))
      (TensorObj.kron (MMObj K 1 q 1)
        (TensorObj.kron (MMObj K 1 1 q) (MMObj K q 1 1))) :=
    TensorQ.mul_respects_iso (TensorObj.Isomorphic.refl _)
      (TensorQ.mul_respects_iso hcyc₁ hcyc₂)
  have hinner : TensorObj.Isomorphic
      (TensorObj.kron (MMObj K 1 1 q) (MMObj K q 1 1))
      (MMObj K (1 * q) (1 * 1) (q * 1)) :=
    MMObj_kron_iso 1 1 q q 1 1
  have hcombine : TensorObj.Isomorphic
      (TensorObj.kron (MMObj K 1 q 1)
        (TensorObj.kron (MMObj K 1 1 q) (MMObj K q 1 1)))
      (TensorObj.kron (MMObj K 1 q 1)
        (MMObj K (1 * q) (1 * 1) (q * 1))) :=
    TensorQ.mul_respects_iso (TensorObj.Isomorphic.refl _) hinner
  have houter : TensorObj.Isomorphic
      (TensorObj.kron (MMObj K 1 q 1)
        (MMObj K (1 * q) (1 * 1) (q * 1)))
      (MMObj K (1 * (1 * q)) (q * (1 * 1)) (1 * (q * 1))) :=
    MMObj_kron_iso 1 q 1 (1 * q) (1 * 1) (q * 1)
  refine TensorObj.Isomorphic.trans hblocks
    (TensorObj.Isomorphic.trans hcombine ?_)
  simpa using houter

end CWCoupledCyclicLowMM

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (MMObj K q q q)
      (cyclicSymmetrization (MMObj K 1 q 1)) := by
  rw [CWCoupledCyclicLowMM.cyclic_eq_public]
  exact (CWCoupledCyclicLowMM.nested_MM_iso q).2
