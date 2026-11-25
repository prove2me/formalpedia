-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_commutator_mem_kJ
-- name    : CompanionTheory.D.Upq.commutator_mem_kJ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:15:50.635311+00:00
-- url     : https://prove2.me/theorems/89570ef3-71a0-4c2d-9996-2e7243bb2f9d
-- title:
--   Upq: commutator mem k J
-- statement:
--   The Upq construction uses the commutator mem k J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L170-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L170-L175

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

theorem CompanionTheory.D.Upq.commutator_mem_kJ {X Y : Matrix n n ℂ} (hX : X ∈ kJ J) (hY : Y ∈ kJ J) :
    X * Y - Y * X ∈ kJ J := by sorry
