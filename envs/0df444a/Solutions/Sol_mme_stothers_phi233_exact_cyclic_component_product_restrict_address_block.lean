-- Prove2me | solution 1 for mme_stothers_phi233_exact_cyclic_component_product_restrict_address_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:56:49.290349+00:00
-- url     : https://prove2.me/submissions/a5761cf0-63de-4c74-b714-9ef2405e747e

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_grading_address
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_tensor_quotient
import Theorems.Thm_mme_cyclic_grading_address_block_iso
import Theorems.Thm_mme_stothers_phi233_exact_component_product_restrict_outer_address_block

open MME

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

private theorem kron_restrict
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  let P := TensorQ.tensorStrassen K d hd
  have hx : TensorQ.le (TensorQ.toQ X) (TensorQ.toQ X') :=
    (TensorQ.le_toQ X X').2 hX
  have hy : TensorQ.le (TensorQ.toQ Y) (TensorQ.toQ Y') :=
    (TensorQ.le_toQ Y Y').2 hY
  have hleft := P.mul_right _ _ hx (TensorQ.toQ Y)
  have hright := P.mul_right _ _ hy (TensorQ.toQ X')
  apply (TensorQ.le_toQ _ _).1
  rw [TensorQ.toQ_kron, TensorQ.toQ_kron]
  exact P.le_trans _ _ _ hleft (by simpa only [mul_comm] using hright)

theorem solution
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (e : MME.StothersFourth.Phi233.CyclicExactEdge
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (cyclicSymmetrization
        (TensorObj.kronFin 10 (fun r ↦
          (MME.StothersFourth.Phi233.componentObj K q r).kronPow
            (MME.StothersFourth.Phi233.profileMultiplicity
              alpha beta gamma delta r))))
      (gradedAddressBlock
        (mmeCyclicTripleGrading
          (MME.StothersFourth.Phi233.outerGrading K q))
        (MME.StothersFourth.Phi233.cyclicGradingAddress
          (MME.StothersFourth.Phi233.exactToAmbient e))) := by
  let P := TensorObj.kronFin 10 (fun r ↦
    (MME.StothersFourth.Phi233.componentObj K q r).kronPow
      (MME.StothersFourth.Phi233.profileMultiplicity
        alpha beta gamma delta r))
  have hA :=
    mme_stothers_phi233_exact_component_product_restrict_outer_address_block
      (K := K) q e.1
  have hB :=
    mme_stothers_phi233_exact_component_product_restrict_outer_address_block
      (K := K) q e.2.1
  have hC :=
    mme_stothers_phi233_exact_component_product_restrict_outer_address_block
      (K := K) q e.2.2
  have hBperm := TensorObj.permObj_restrict cyclicPerm hB
  have hCperm := TensorObj.permObj_restrict
    (cyclicPerm.trans cyclicPerm) hC
  have hsource : TensorObj.Restrict
      (TensorObj.kron P
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm P)
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) P)))
      (TensorObj.kron
        (gradedAddressBlock
          (MME.StothersFourth.Phi233.outerGrading K q) e.1.1.1)
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm
            (gradedAddressBlock
              (MME.StothersFourth.Phi233.outerGrading K q) e.2.1.1.1))
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (gradedAddressBlock
              (MME.StothersFourth.Phi233.outerGrading K q) e.2.2.1.1)))) := by
    apply kron_restrict (K := K) (by omega) hA
    exact kron_restrict (K := K) (by omega) hBperm hCperm
  have hword := mme_cyclic_grading_address_block_iso
    (MME.StothersFourth.Phi233.outerGrading K q)
    e.1.1.1 e.2.1.1.1 e.2.2.1.1
  rw [cyclicSymmetrization_eq_public_perm]
  exact TensorObj.Restrict.trans hsource hword.1
