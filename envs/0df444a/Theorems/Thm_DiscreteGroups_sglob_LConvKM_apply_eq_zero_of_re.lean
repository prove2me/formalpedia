-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvKM_apply_eq_zero_of_re
-- name    : DiscreteGroups.sglob.LConvKM.apply_eq_zero_of_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:26.081145+00:00
-- url     : https://prove2.me/theorems/b10ed6d8-db37-4fa3-b8eb-81aaf6d898ad
-- title:
--   LConv KM: apply eq zero of re
-- statement:
--   The LConv KM construction uses the apply eq zero of re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L81-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L81-L104

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set ComplexConjugate
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open DiscreteGroups DiscreteGroups.sglob DiscreteGroups.sglob.LConvKM
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)

theorem DiscreteGroups.sglob.LConvKM.apply_eq_zero_of_re (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (psd : ∀ x, 0 ≤ (B x x).re)
    (u : M) (hu : (B u u).re = 0) (y : M) : B u y = 0 := by sorry
