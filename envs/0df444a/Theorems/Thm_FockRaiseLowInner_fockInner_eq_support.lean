-- Prove2me | Theorems.Thm_FockRaiseLowInner_fockInner_eq_support
-- name    : FockRaiseLowInner.fockInner_eq_support
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:58.229673+00:00
-- url     : https://prove2.me/theorems/e095b809-39b1-430b-ad5f-2e11eca1348a
-- title:
--   Fock Raise Low Inner: fock Inner eq support
-- statement:
--   The Fock Raise Low Inner construction uses the fock Inner eq support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L15-L27

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

theorem FockRaiseLowInner.fockInner_eq_support (P Q : MvPolynomial σ ℂ) :
    fockInner P Q = ∑ α ∈ P.support, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by sorry
