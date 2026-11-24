-- Prove2me | Theorems.Thm_FockRaiseLowInner_wt_single_add
-- name    : FockRaiseLowInner.wt_single_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:24.361457+00:00
-- url     : https://prove2.me/theorems/cb398e0d-f502-43d7-9b12-ebff7ebb4e9d
-- title:
--   Fock Raise Low Inner: wt single add
-- statement:
--   The Fock Raise Low Inner construction uses the wt single add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L157-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L157-L188

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

theorem FockRaiseLowInner.wt_single_add (l : σ) (α : σ →₀ ℕ) :
    wt (Finsupp.single l 1 + α) = ((α l : ℂ) + 1) * wt α := by sorry
