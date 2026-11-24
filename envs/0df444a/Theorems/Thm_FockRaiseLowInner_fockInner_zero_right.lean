-- Prove2me | Theorems.Thm_FockRaiseLowInner_fockInner_zero_right
-- name    : FockRaiseLowInner.fockInner_zero_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:50.182858+00:00
-- url     : https://prove2.me/theorems/e7fc3e5a-2688-4f93-be0d-dfb5e8e61dee
-- title:
--   Fock Raise Low Inner: fock Inner zero right
-- statement:
--   The Fock Raise Low Inner construction uses the fock Inner zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L69-L71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockRaiseLowInner
open MvPolynomial FockH1Action
variable {σ : Type*}

theorem FockRaiseLowInner.fockInner_zero_right (P : MvPolynomial σ ℂ) : fockInner P 0 = 0 := by sorry
