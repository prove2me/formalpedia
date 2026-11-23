-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvKM_mkForm_apply
-- name    : DiscreteGroups.sglob.LConvKM.mkForm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:54.342166+00:00
-- url     : https://prove2.me/theorems/9e14c8c9-4abe-4385-921a-e48a9ed27ca6
-- title:
--   LConv KM: mk Form apply
-- statement:
--   The LConv KM construction uses the mk Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L139-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L139-L140

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

theorem DiscreteGroups.sglob.LConvKM.mkForm_apply (F : M → M → ℂ) (h : F ∈ (sesqSet : Set (M → M → ℂ))) (x y : M) :
    mkForm F h x y = F x y := by sorry

attribute [defeq] DiscreteGroups.sglob.LConvKM.mkForm_apply
