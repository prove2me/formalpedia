-- Prove2me | Theorems.Thm_FockRaiseLowInner_fockInner_sum_right
-- name    : FockRaiseLowInner.fockInner_sum_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:14.29585+00:00
-- url     : https://prove2.me/theorems/2e3ed6f4-d27d-4611-b18c-8141b4f91e77
-- title:
--   Fock Raise Low Inner: fock Inner sum right
-- statement:
--   The Fock Raise Low Inner construction uses the fock Inner sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L126-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L126-L133

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

theorem FockRaiseLowInner.fockInner_sum_right {ι : Type*} (s : Finset ι) (P : MvPolynomial σ ℂ)
    (f : ι → MvPolynomial σ ℂ) :
    fockInner P (∑ i ∈ s, f i) = ∑ i ∈ s, fockInner P (f i) := by sorry
