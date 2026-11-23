-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_conjTranspose_mem_lieJ
-- name    : CompanionTheory.D.Upq.conjTranspose_mem_lieJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:57.894945+00:00
-- url     : https://prove2.me/theorems/a303d917-d99b-43ce-928a-e830bed35fee
-- title:
--   Upq: conj Transpose mem lie J
-- statement:
--   The Upq construction uses the conj Transpose mem lie J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L84-L88

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
variable {J : Matrix n n ℂ} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ

theorem CompanionTheory.D.Upq.conjTranspose_mem_lieJ {X : Matrix n n ℂ} (hX : X ∈ lieJ J) : Xᴴ ∈ lieJ J := by sorry
