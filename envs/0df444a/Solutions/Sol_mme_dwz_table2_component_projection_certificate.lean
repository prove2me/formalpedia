-- Prove2me | solution 1 for mme_dwz_table2_component_projection_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T08:09:02.31675+00:00
-- url     : https://prove2.me/submissions/6d26caac-7f2b-4e49-8def-d7939f5ad7b9

import Definitions.Def_mme_dwz_component_word_projection
import Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ) :
    TensorObj.Restrict
        (MME.DWZComponentRestriction.restrictedComponentPower K s m)
        ((MME.DWZComponentRestriction.canonicalComponentBlock K s).kronPow
          (MME.DWZTable2Counts.component s * m)) ∧
      (MME.DWZComponentRestriction.componentPowerProjectionGrading K s m).classOf
          0 0 = ⊤ ∧
      (MME.DWZComponentRestriction.componentPowerProjectionGrading K s m).classOf
          1 0 = ⊤ ∧
      (MME.DWZComponentRestriction.componentPowerProjectionGrading K s m).classOf
          2 0 =
        Submodule.span K
          (MME.DWZComponentRestriction.componentPowerZBasis K s m ''
            {w | MME.DWZComponentRestriction.componentWordAllowed s m w}) := by
  classical
  let : DecidablePred
      (MME.DWZComponentRestriction.componentWordAllowed s m) :=
    Classical.decPred _
  exact
    (mme_basisZAllowedSubtensor_projection_certificate
      (T := (MME.DWZComponentRestriction.canonicalComponentBlock K s).kronPow
        (MME.DWZTable2Counts.component s * m))
      (bZ := MME.DWZComponentRestriction.componentPowerZBasis K s m)
      (allowed := MME.DWZComponentRestriction.componentWordAllowed s m))
