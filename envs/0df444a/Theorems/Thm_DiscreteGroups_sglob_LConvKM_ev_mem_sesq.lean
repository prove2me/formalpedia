-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvKM_ev_mem_sesq
-- name    : DiscreteGroups.sglob.LConvKM.ev_mem_sesq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:30.492824+00:00
-- url     : https://prove2.me/theorems/ca9ccc40-f72f-4de8-be36-85dd97672b7c
-- title:
--   LConv KM: ev mem sesq
-- statement:
--   The LConv KM construction uses the ev mem sesq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L142-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L142-L144

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

theorem DiscreteGroups.sglob.LConvKM.ev_mem_sesq (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : ev B ∈ (sesqSet : Set (M → M → ℂ)) := by sorry
