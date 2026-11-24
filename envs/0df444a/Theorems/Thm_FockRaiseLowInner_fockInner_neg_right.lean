-- Prove2me | Theorems.Thm_FockRaiseLowInner_fockInner_neg_right
-- name    : FockRaiseLowInner.fockInner_neg_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:31.344441+00:00
-- url     : https://prove2.me/theorems/35e2e324-86bb-4f65-acd6-368fd4abb28e
-- title:
--   Fock Raise Low Inner: fock Inner neg right
-- statement:
--   The Fock Raise Low Inner construction uses the fock Inner neg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L88-L93

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

theorem FockRaiseLowInner.fockInner_neg_right (P Q : MvPolynomial σ ℂ) :
    fockInner P (-Q) = - fockInner P Q := by sorry
