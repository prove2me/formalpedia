-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_polar_mem_UJ
-- name    : CompanionTheory.D.Upq.polar_mem_UJ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:44:33.979098+00:00
-- url     : https://prove2.me/theorems/17591f7c-3236-47a1-8096-398b9b4ef4ac
-- title:
--   Upq: polar mem UJ
-- statement:
--   The Upq construction uses the polar mem UJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/PolarUH.lean#L66-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/PolarUH.lean#L66-L77

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

theorem CompanionTheory.D.Upq.polar_mem_UJ (hJJ : J * J = 1) (hJh : Jᴴ = J) (g : GL m ℂ)
    (hg : (g : Matrix m m ℂ)ᴴ * J * g = J) :
    (polarPos g)ᴴ * J * polarPos g = J ∧ (polarUnitary g)ᴴ * J * polarUnitary g = J := by sorry
