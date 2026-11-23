-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_reG_add_I_smul_imG
-- name    : CompanionTheory.D.Upq.reG_add_I_smul_imG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:57.11328+00:00
-- url     : https://prove2.me/theorems/055af67e-e895-4e06-884f-48fbfbc66574
-- title:
--   Upq: re G add I smul im G
-- statement:
--   The Upq construction uses the re G add I smul im G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L250-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L250-L254

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
variable (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ hJh
omit hJ hJh

theorem CompanionTheory.D.Upq.reG_add_I_smul_imG (M : Matrix n n ℂ) : M = reG J M + Complex.I • imG J M := by sorry
