-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_lie_mem_lieSubJ
-- name    : CompanionTheory.D.Upq.lie_mem_lieSubJ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:58.341876+00:00
-- url     : https://prove2.me/theorems/72ccc9de-63be-49a7-85e3-8fac40f59dde
-- title:
--   Upq: lie mem lie Sub J
-- statement:
--   The Upq construction uses the lie mem lie Sub J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L58-L60

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
variable {J}

theorem CompanionTheory.D.Upq.lie_mem_lieSubJ {X Y : Matrix n n ℂ} (hX : X ∈ lieSubJ J) (hY : Y ∈ lieSubJ J) :
    ⁅X, Y⁆ ∈ lieSubJ J := by sorry
