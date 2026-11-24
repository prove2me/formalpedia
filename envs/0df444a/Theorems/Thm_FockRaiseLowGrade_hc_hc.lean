-- Prove2me | Theorems.Thm_FockRaiseLowGrade_hc_hc
-- name    : FockRaiseLowGrade.hc_hc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:19.657967+00:00
-- url     : https://prove2.me/theorems/2e9cfea2-33c4-4d8f-8022-df0baad48fba
-- title:
--   Fock Raise Low Grade: hc hc
-- statement:
--   The Fock Raise Low Grade construction uses the hc hc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/RaisingLoweringSplit.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/RaisingLoweringSplit.lean#L13-L17

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

theorem FockRaiseLowGrade.hc_hc (m n : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent m (homogeneousComponent n P) =
      if m = n then homogeneousComponent n P else 0 := by sorry
