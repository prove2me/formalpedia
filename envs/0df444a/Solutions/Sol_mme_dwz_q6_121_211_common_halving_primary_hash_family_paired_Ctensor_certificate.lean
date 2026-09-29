-- Prove2me | solution 1 for mme_dwz_q6_121_211_common_halving_primary_hash_family_paired_Ctensor_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:12:25.545878+00:00
-- url     : https://prove2.me/submissions/03d72b32-2a12-406b-b19a-f781539a6dc2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Theorems.Thm_mme_dwz_q6_121_211_common_halving_ambient_Ctensor_mode_choice_certificate
import Theorems.Thm_mme_dwz_component_pair_projection_inclusion_tensor
import Theorems.Thm_mme_induced_mode_choice_certificate_descent
import Theorems.Thm_mme_induced_mode_choice_certificate_restrict

open MME PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem core
    {K : Type u} [Field K]
    (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (MME.DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving) :
    Nonempty (CTensorOneHOneFamilyCertificate
      (componentPairRestricted K s m)
      A H (6 ^ (4 * G + 2 * L))) := by
  obtain ⟨star, ambientCert, habsorb, ⟨starCert⟩⟩ :=
    mme_dwz_q6_121_211_common_halving_ambient_Ctensor_mode_choice_certificate
      (K := K) s hs m L G A H family halving
  obtain ⟨restrictedCert⟩ :=
    mme_induced_mode_choice_certificate_descent ambientCert
      (componentPairInclusion K s m)
      (componentPairProject K s m)
      (mme_dwz_component_pair_projection_inclusion_tensor s m)
      habsorb
  refine ⟨{
    star := star
    restrict := ?_
    certificate := starCert
  }⟩
  exact mme_induced_mode_choice_certificate_restrict restrictedCert

theorem solution
    {K : Type u} [Field K]
    (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (MME.DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving) :
    Nonempty (CTensorOneHOneFamilyCertificate
      (TensorObj.kron (restrictedComponentPower K s m)
        (TensorObj.permObj swapFirstTwoPerm
          (restrictedComponentPower K s m)))
      A H (6 ^ (4 * G + 2 * L))) := by
  simpa only [componentPairRestricted] using
    (core (K := K) s hs m L G A H family halving)
