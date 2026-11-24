-- Prove2me | Theorems.Thm_FockRaiseLowInner_fockInner_eq_sum
-- name    : FockRaiseLowInner.fockInner_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:08.955974+00:00
-- url     : https://prove2.me/theorems/9a7597f8-3227-42ef-9079-ec28a8008b20
-- title:
--   Fock Raise Low Inner: fock Inner eq sum
-- statement:
--   The Fock Raise Low Inner construction uses the fock Inner eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L29-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L29-L44

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

theorem FockRaiseLowInner.fockInner_eq_sum (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : ∀ α, α ∉ S → (starRingEnd ℂ) (coeff α P) * coeff α Q = 0) :
    fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by sorry
