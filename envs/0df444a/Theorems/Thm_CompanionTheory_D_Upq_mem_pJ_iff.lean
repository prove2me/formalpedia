-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_mem_pJ_iff
-- name    : CompanionTheory.D.Upq.mem_pJ_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:39.365507+00:00
-- url     : https://prove2.me/theorems/020b55ae-7d88-4317-8c73-4ca98f995683
-- title:
--   Upq: mem p J iff
-- statement:
--   The Upq construction uses the mem p J iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L138-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L138-L146

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (J : Matrix n n ℂ)
variable {J} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ

theorem CompanionTheory.D.Upq.mem_pJ_iff {X : Matrix n n ℂ} : X ∈ pJ J ↔ X ∈ lieJ J ∧ Xᴴ = X := by sorry
