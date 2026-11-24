-- Prove2me | Theorems.Thm_FockRaiseLowInner_fockInner_add_left
-- name    : FockRaiseLowInner.fockInner_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:57.353909+00:00
-- url     : https://prove2.me/theorems/a548cad0-b0fe-45fb-940d-474a1724e927
-- title:
--   Fock Raise Low Inner: fock Inner add left
-- statement:
--   The Fock Raise Low Inner construction uses the fock Inner add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean#L103-L109

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

theorem FockRaiseLowInner.fockInner_add_left (P₁ P₂ Q : MvPolynomial σ ℂ) :
    fockInner (P₁ + P₂) Q = fockInner P₁ Q + fockInner P₂ Q := by sorry
