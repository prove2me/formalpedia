-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_mul_J_mul_conjTranspose
-- name    : CompanionTheory.D.Upq.mul_J_mul_conjTranspose
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:44:48.703973+00:00
-- url     : https://prove2.me/theorems/3b714068-dd9d-4664-8ecc-769874143f83
-- title:
--   Upq: mul J mul conj Transpose
-- statement:
--   The Upq construction uses the mul J mul conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/PolarUH.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/PolarUH.lean#L14-L21

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_CoePolarExpHomeomorphComplexApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_PolarUH
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
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
set_option linter.unusedSectionVars false
variable {m : Type*} [Fintype m] [DecidableEq m] {J : Matrix m m ℂ}

theorem CompanionTheory.D.Upq.mul_J_mul_conjTranspose (hJJ : J * J = 1) {g : Matrix m m ℂ} (hg : gᴴ * J * g = J) :
    g * J * gᴴ = J := by sorry
