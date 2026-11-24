-- Prove2me | Theorems.Thm_FockRaiseLowInner_fockInner_mul_X
-- name    : FockRaiseLowInner.fockInner_mul_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:13.875389+00:00
-- url     : https://prove2.me/theorems/175781d0-4ac0-4dcf-89fe-434ec0fbf0da
-- title:
--   Fock Raise Low Inner: fock Inner mul X
-- statement:
--   The Fock Raise Low Inner construction uses the fock Inner mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L219-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L219-L221

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

theorem FockRaiseLowInner.fockInner_mul_X (l : σ) (P Q : MvPolynomial σ ℂ) :
    fockInner P (X l * Q) = fockInner (pderiv l P) Q := by sorry
