-- Prove2me | Theorems.Thm_FockRaiseLowInner_fischerXAdjoint
-- name    : FockRaiseLowInner.fischerXAdjoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:25.264802+00:00
-- url     : https://prove2.me/theorems/8b82ed52-4906-46b9-8880-8fb263a66f7b
-- title:
--   Fock Raise Low Inner: fischer XAdjoint
-- statement:
--   The Fock Raise Low Inner construction uses the fischer XAdjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L231-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L231-L233

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

theorem FockRaiseLowInner.fischerXAdjoint : FockRL.FockXAdj := by sorry
