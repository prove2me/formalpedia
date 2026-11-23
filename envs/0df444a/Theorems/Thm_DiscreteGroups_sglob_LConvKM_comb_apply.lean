-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvKM_comb_apply
-- name    : DiscreteGroups.sglob.LConvKM.comb_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:55.915951+00:00
-- url     : https://prove2.me/theorems/79de3311-781b-4c74-90bf-0397c8c0fcf9
-- title:
--   LConv KM: comb apply
-- statement:
--   The LConv KM construction uses the comb apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L125-L127

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

theorem DiscreteGroups.sglob.LConvKM.comb_apply (F G : M → M → ℂ) (a b : ℝ) (x y : M) :
    (a • F + b • G) x y = (a : ℂ) * F x y + (b : ℂ) * G x y := by sorry
