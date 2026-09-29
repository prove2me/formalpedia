-- Prove2me | solution 1 for mme_dwz_fine_z_unique_owner_direct_sum_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T19:45:24.872884+00:00
-- url     : https://prove2.me/submissions/211bf185-de60-47dd-941c-28f3dcf187c1

import Theorems.Thm_mme_induced_graded_address_blocks_restrict

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t N k : ℕ}
    (G : T.TypeGrading t)
    (fineAddress : Fin k → Fin 3 → Fin N → Fin t)
    (fineZOwner : (Fin N → Fin t) → Option (Fin k))
    (hOwned : ∀ j : Fin k,
      fineZOwner (fineAddress j 2) = some j)
    (hXYOwner : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      js 0 = js 1)
    (hSupportedFineZOwner : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      fineZOwner (fineAddress (js 2) 2) = some (js 0)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ gradedAddressBlock G (fineAddress j)))
      (T.kronPow N) := by
  apply mme_induced_graded_address_blocks_restrict G fineAddress
  intro js hsupported
  have hxy : js 0 = js 1 := hXYOwner js hsupported
  have hzOwner : (some (js 2) : Option (Fin k)) = some (js 0) := by
    rw [← hOwned (js 2)]
    exact hSupportedFineZOwner js hsupported
  have hzx : js 2 = js 0 := Option.some.inj hzOwner
  refine ⟨js 0, ?_⟩
  funext i
  fin_cases i
  · rfl
  · exact hxy.symm
  · exact hzx
