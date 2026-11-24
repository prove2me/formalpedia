-- Prove2me | Theorems.Thm_FockRaiseLowGrade_sum_hc_of_le
-- name    : FockRaiseLowGrade.sum_hc_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:35.223241+00:00
-- url     : https://prove2.me/theorems/ed06b857-354c-4a3d-987d-501b67d00725
-- title:
--   Fock Raise Low Grade: sum hc of le
-- statement:
--   The Fock Raise Low Grade construction uses the sum hc of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/RaisingLoweringSplit.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/RaisingLoweringSplit.lean#L25-L36

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

theorem FockRaiseLowGrade.sum_hc_of_le (P : MvPolynomial σ ℂ) (n : ℕ) (hn : P.totalDegree < n) :
    ∑ i ∈ Finset.range n, homogeneousComponent i P = P := by sorry
