-- Prove2me | solution 1 for mme_induced_mode_choice_certificate_precompose_restrict
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:52:50.389659+00:00
-- url     : https://prove2.me/submissions/f879e22c-7abb-4a39-8c98-7774fa5848d4

import Definitions.Def_mme_induced_mode_choice_certificate
import Definitions.Def_mme_tensor_rank

open MME PiTensorProduct BigOperators

universe uCertificate
set_option autoImplicit false

theorem solution
    {K : Type uCertificate} [Field K]
    {source middle target : TensorObj K 3}
    (hMiddle : TensorObj.Restrict middle source)
    (hCert : Nonempty (InducedModeChoiceCertificate middle target)) :
    Nonempty (InducedModeChoiceCertificate source target) := by
  classical
  obtain ⟨f, hf⟩ := hMiddle
  obtain ⟨cert⟩ := hCert
  refine ⟨{
    slotCount := cert.slotCount
    modeMap := fun i j => cert.modeMap i j ∘ₗ f i
    kept := cert.kept
    offSupport := ?_
    targetTensor := ?_
  }⟩
  · intro choice hchoice
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hf]
    exact cert.offSupport choice hchoice
  · simpa only [PiTensorProduct.map_comp, LinearMap.comp_apply, hf] using
      cert.targetTensor
