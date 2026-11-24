-- Prove2me | Theorems.Thm_FockRaiseLowInner_fockInner_sum_left
-- name    : FockRaiseLowInner.fockInner_sum_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:07.112858+00:00
-- url     : https://prove2.me/theorems/52c3fd46-5f5a-4b59-99c0-75cbf9b1b532
-- title:
--   Fock Raise Low Inner: fock Inner sum left
-- statement:
--   The Fock Raise Low Inner construction uses the fock Inner sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L135-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L135-L142

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

theorem FockRaiseLowInner.fockInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (Q : MvPolynomial σ ℂ) :
    fockInner (∑ i ∈ s, f i) Q = ∑ i ∈ s, fockInner (f i) Q := by sorry
