-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvKM_im_diag
-- name    : DiscreteGroups.sglob.LConvKM.im_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:26.486507+00:00
-- url     : https://prove2.me/theorems/06f1deda-2360-49a8-afe8-b409cd2b2d40
-- title:
--   LConv KM: im diag
-- statement:
--   The LConv KM construction uses the im diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L30-L33

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

theorem DiscreteGroups.sglob.LConvKM.im_diag (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (x : M) : (B x x).im = 0 := by sorry
