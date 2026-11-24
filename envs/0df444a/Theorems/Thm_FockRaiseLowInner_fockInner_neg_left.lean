-- Prove2me | Theorems.Thm_FockRaiseLowInner_fockInner_neg_left
-- name    : FockRaiseLowInner.fockInner_neg_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:16.808611+00:00
-- url     : https://prove2.me/theorems/649e4b0d-97d3-42b2-a5e9-25eb349fd2e6
-- title:
--   Fock Raise Low Inner: fock Inner neg left
-- statement:
--   The Fock Raise Low Inner construction uses the fock Inner neg left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L118-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L118-L124

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

theorem FockRaiseLowInner.fockInner_neg_left (P Q : MvPolynomial σ ℂ) :
    fockInner (-P) Q = - fockInner P Q := by sorry
