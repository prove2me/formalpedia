-- Prove2me | solution 1 for mme_dwz_step2_nonholes_direct_sum_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:24:44.155973+00:00
-- url     : https://prove2.me/submissions/360c97be-9417-4daa-83d2-b2b19c9d3641

import Definitions.Def_mme_dwz_step2_broken_copy
import Theorems.Thm_mme_dwz_fine_z_compatibility_direct_sum_restrict

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t N k : ℕ}
    (G : T.TypeGrading t)
    (fineAddress : Fin k → Fin 3 → Fin N → Fin t)
    (compatible useful : (Fin N → Fin t) → Fin k → Prop)
    [DecidableRel compatible] [DecidableRel useful]
    (hNonhole : ∀ j : Fin k,
      fineAddress j 2 ∈
        (MME.DWZStep2.brokenCopy compatible useful j).nonholes)
    (hXYOwner : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      js 0 = js 1)
    (hSupportedCompatible : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      compatible (fineAddress (js 2) 2) (js 0)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ gradedAddressBlock G (fineAddress j)))
      (T.kronPow N) := by
  classical
  have hKeeps : ∀ j : Fin k,
      useful (fineAddress j 2) j ∧
        compatible (fineAddress j 2) j ∧
          ∀ j', compatible (fineAddress j 2) j' → j' = j := by
    intro j
    have h := hNonhole j
    simp only [MME.DWZStep2.brokenCopy, Finset.mem_filter,
      Finset.mem_univ, true_and] at h
    exact h
  exact mme_dwz_fine_z_compatibility_direct_sum_restrict
    G fineAddress compatible
    (fun j ↦ (hKeeps j).2.1)
    (fun j j' hj' ↦ (hKeeps j).2.2 j' hj')
    hXYOwner hSupportedCompatible
