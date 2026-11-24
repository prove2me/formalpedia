-- Prove2me | Theorems.Thm_FockRaiseLowInner_fockInner_add_right
-- name    : FockRaiseLowInner.fockInner_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:01.664968+00:00
-- url     : https://prove2.me/theorems/be696310-61f6-4570-9280-3284395c6c7a
-- title:
--   Fock Raise Low Inner: fock Inner add right
-- statement:
--   The Fock Raise Low Inner construction uses the fock Inner add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L73-L79

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

theorem FockRaiseLowInner.fockInner_add_right (P Q₁ Q₂ : MvPolynomial σ ℂ) :
    fockInner P (Q₁ + Q₂) = fockInner P Q₁ + fockInner P Q₂ := by sorry
