-- Prove2me | solution 1 for mme_Ctensor_induced_matching_survivor_grading_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T16:19:48.092754+00:00
-- url     : https://prove2.me/submissions/0f41c89a-50f5-40fa-aab9-8135db6056d3

import Theorems.Thm_mme_Ctensor_induced_matching_distribute_survivors
import Theorems.Thm_mme_diagObj_kron_canonical_grading_certificate

open MME BigOperators

universe u

theorem solution
    {K : Type u} [Field K]
    (T : TensorObj K 3) (L G A H k : ℕ)
    (hmacro :
      TensorObj.Restrict
        (TensorObj.bigAdd (fun _ : Fin (A ^ 3) =>
          TensorObj.kron (MMObj K H H H)
            (coupledQ6Survivor K L G)))
        T)
    (hmatching :
      TensorObj.Restrict
        (TensorObj.bigAdd (fun _ : Fin k => MMObj K 1 1 1))
        (MMObj K H H H)) :
    ∃ (P : TensorObj K 3) (t : ℕ) (grading : P.TypeGrading t)
        (C : Finset (Fin 3 → Fin t))
        (σs : Fin C.card → (Fin 3 → Fin t)),
      TensorObj.Restrict P T ∧
      (∀ j, σs j ∈ C) ∧
      Function.Injective σs ∧
      (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' →
        ∀ i : Fin 3, σ i ≠ σ' i) ∧
      (∀ σ : Fin 3 → Fin t, σ ∉ C → grading.blockTensor σ = 0) ∧
      (∀ j, TensorObj.Restrict
        (coupledQ6Survivor K L G)
        (grading.blockSubtensor (σs j))) ∧
      C.card = (A ^ 3) * k := by
  let P : TensorObj K 3 :=
    TensorObj.kron
      (TensorObj.diagObj K 3 ((A ^ 3) * k))
      (coupledQ6Survivor K L G)
  have hP : TensorObj.Restrict P T := by
    exact mme_Ctensor_induced_matching_distribute_survivors
      T L G A H k hmacro hmatching
  obtain ⟨t, grading, C, σs, hmem, hinj, hdisj, hsupp, hblocks,
      hcard⟩ :=
    mme_diagObj_kron_canonical_grading_certificate
      (coupledQ6Survivor K L G) ((A ^ 3) * k)
  exact ⟨P, t, grading, C, σs, hP, hmem, hinj, hdisj, hsupp, hblocks,
    hcard⟩
