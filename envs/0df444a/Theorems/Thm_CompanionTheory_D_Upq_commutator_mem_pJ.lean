-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_commutator_mem_pJ
-- name    : CompanionTheory.D.Upq.commutator_mem_pJ
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:15:48.731887+00:00
-- url     : https://prove2.me/theorems/9486b906-b8c4-44e9-a0b6-6beeb6f6a1cf
-- title:
--   Upq: commutator mem p J
-- statement:
--   The Upq construction uses the commutator mem p J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L177-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L177-L182

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

theorem CompanionTheory.D.Upq.commutator_mem_pJ {X Y : Matrix n n ℂ} (hX : X ∈ kJ J) (hY : Y ∈ pJ J) :
    X * Y - Y * X ∈ pJ J := by sorry
