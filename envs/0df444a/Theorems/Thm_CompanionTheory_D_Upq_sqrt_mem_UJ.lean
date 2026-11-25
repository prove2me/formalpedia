-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_sqrt_mem_UJ
-- name    : CompanionTheory.D.Upq.sqrt_mem_UJ
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:06:10.643625+00:00
-- url     : https://prove2.me/theorems/6ea46830-dc74-48a2-a2ee-55ef4430b1d8
-- title:
--   Upq: sqrt mem UJ
-- statement:
--   The Upq construction uses the sqrt mem UJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/PolarUH.lean#L23-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/PolarUH.lean#L23-L52

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

theorem CompanionTheory.D.Upq.sqrt_mem_UJ (hJJ : J * J = 1) (hJh : Jᴴ = J) {P : Matrix m m ℂ} (hP : P.PosDef)
    (hPJ : Pᴴ * J * P = J) : (CFC.sqrt P)ᴴ * J * CFC.sqrt P = J := by sorry
