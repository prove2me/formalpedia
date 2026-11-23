-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_J_mul_mul_J_of_mem
-- name    : CompanionTheory.D.Upq.J_mul_mul_J_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:53.09204+00:00
-- url     : https://prove2.me/theorems/5e3f9de8-1aff-4b6e-9517-cca424ea4a9d
-- title:
--   Upq: J mul mul J of mem
-- statement:
--   The Upq construction uses the J mul mul J of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L90-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L90-L91

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

theorem CompanionTheory.D.Upq.J_mul_mul_J_of_mem {X : Matrix n n ℂ} (hX : X ∈ lieJ J) : J * X * J = -Xᴴ := by sorry
