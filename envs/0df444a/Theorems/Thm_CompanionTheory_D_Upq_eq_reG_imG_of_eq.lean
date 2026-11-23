-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_eq_reG_imG_of_eq
-- name    : CompanionTheory.D.Upq.eq_reG_imG_of_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:56.20317+00:00
-- url     : https://prove2.me/theorems/ec9e7c9e-ae4c-4d66-aa63-c5e59d3bafe6
-- title:
--   Upq: eq re G im G of eq
-- statement:
--   The Upq construction uses the eq re G im G of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L256-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ExistsUniqueComplexification.lean#L256-L266

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

theorem CompanionTheory.D.Upq.eq_reG_imG_of_eq {M X Y : Matrix n n ℂ} (hX : X ∈ lieJ J) (hY : Y ∈ lieJ J)
    (hM : M = X + Complex.I • Y) : X = reG J M ∧ Y = imG J M := by sorry
