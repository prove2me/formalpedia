-- Prove2me | solution 1 for mme_dwz_q6_121_211_primary_hash_family_MM_restrict_of_star_landing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:06:44.521479+00:00
-- url     : https://prove2.me/submissions/042ef75b-0e0e-45be-b16b-ddfce057af4d

import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_CW_q6_primary_star_cyclic_hash_fiber_assembly
import Theorems.Thm_mme_CW_q6_coupled_survivors_assemble_MM

open MME BigOperators
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K]
    (s : Fin 15) (m L G A H : ℕ)
    (hstars : TensorObj.Restrict
      (cyclicSymmetrization
        (TensorObj.bigAdd (fun _ : Fin A ↦
          TensorObj.kron (MMObj K 1 H 1)
            (coupledQ6OrientedSurvivor K L G))))
      (sixSymmetrization (restrictedComponentPower K s m))) :
    let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin (A ^ 3) ↦
        MMObj K (H * side) (H * side) (H * side)))
      (sixSymmetrization (restrictedComponentPower K s m)) := by
  dsimp only
  let macroObj : TensorObj K 3 :=
    TensorObj.bigAdd (fun _ : Fin (A ^ 3) ↦
      TensorObj.kron (MMObj K H H H) (coupledQ6Survivor K L G))
  have hcyclic : TensorObj.Restrict macroObj
      (cyclicSymmetrization
        (TensorObj.bigAdd (fun _ : Fin A ↦
          TensorObj.kron (MMObj K 1 H 1)
            (coupledQ6OrientedSurvivor K L G)))) := by
    exact mme_CW_q6_primary_star_cyclic_hash_fiber_assembly L G A H
  have hmacro : TensorObj.Restrict macroObj
      (sixSymmetrization (restrictedComponentPower K s m)) :=
    TensorObj.Restrict.trans hcyclic hstars
  let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
  have hsurvivor := mme_CW_q6_coupled_survivors_assemble_MM
    (K := K) L G (A ^ 3)
  let P := TensorQ.tensorStrassen K 3 (by norm_num)
  have hsurvivorQ : P.le
      (TensorQ.toQ
        (TensorObj.bigAdd (fun _ : Fin (A ^ 3) ↦
          MMObj K side side side)))
      (TensorQ.toQ
        (TensorObj.bigAdd (fun _ : Fin (A ^ 3) ↦
          coupledQ6Survivor K L G))) := by
    exact hsurvivor
  have hmul := P.mul_right _ _ hsurvivorQ
    (TensorQ.toQ (MMObj K H H H))
  have hmm : TensorQ.toQ
      (TensorObj.kron (MMObj K H H H) (MMObj K side side side)) =
      TensorQ.toQ (MMObj K (H * side) (H * side) (H * side)) :=
    TensorQ.toQ_eq_iff.mpr
      (MMObj_kron_iso (K := K) H H H side side side)
  have hfinal : TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin (A ^ 3) ↦
        MMObj K (H * side) (H * side) (H * side))) macroObj := by
    change P.le
      (TensorQ.toQ
        (TensorObj.bigAdd (fun _ : Fin (A ^ 3) ↦
          MMObj K (H * side) (H * side) (H * side))))
      (TensorQ.toQ macroObj)
    rw [TensorQ.toQ_bigAdd, TensorQ.toQ_bigAdd]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
      TensorQ.toQ_kron]
    rw [← hmm]
    rw [TensorQ.toQ_kron]
    simpa only [TensorQ.toQ_bigAdd, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul, TensorQ.toQ_kron, mul_assoc, mul_left_comm, mul_comm]
      using hmul
  exact TensorObj.Restrict.trans hfinal hmacro
