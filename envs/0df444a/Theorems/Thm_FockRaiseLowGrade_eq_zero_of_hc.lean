-- Prove2me | Theorems.Thm_FockRaiseLowGrade_eq_zero_of_hc
-- name    : FockRaiseLowGrade.eq_zero_of_hc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:00.488299+00:00
-- url     : https://prove2.me/theorems/3e7cca47-d9b6-43e3-95c0-d710971cb3a8
-- title:
--   Fock Raise Low Grade: eq zero of hc
-- statement:
--   The Fock Raise Low Grade construction uses the eq zero of hc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/RaisingLoweringSplit.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/RaisingLoweringSplit.lean#L19-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockRaiseLowGrade
open MvPolynomial FockH1Action
variable {σ : Type*}

theorem FockRaiseLowGrade.eq_zero_of_hc (x : MvPolynomial σ ℂ) (h : ∀ e, homogeneousComponent e x = 0) :
    x = 0 := by sorry
