-- Prove2me | Theorems.Thm_FockRaiseLowInner_fockInner_eq_sum_left
-- name    : FockRaiseLowInner.fockInner_eq_sum_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:41.464007+00:00
-- url     : https://prove2.me/theorems/a65a0296-33a3-4b55-86af-2a97f8a9cb2c
-- title:
--   Fock Raise Low Inner: fock Inner eq sum left
-- statement:
--   The Fock Raise Low Inner construction uses the fock Inner eq sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L46-L54

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

theorem FockRaiseLowInner.fockInner_eq_sum_left (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) :
    fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by sorry
