-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_sum_padicVal_shift_eq_factorial
-- name    : Formalism.CohomologicalDescent.UnitNormBounds.sum_padicVal_shift_eq_factorial
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:00:37.234258+00:00
-- url     : https://prove2.me/theorems/fc4a377a-c68a-4143-b447-0ea62504cf95
-- title:
--   Unit Norm Bounds: sum padic Val shift eq factorial
-- statement:
--   The Unit Norm Bounds construction uses the sum padic Val shift eq factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/UnitNormBounds.lean#L281-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/UnitNormBounds.lean#L281-L304

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD

theorem Formalism.CohomologicalDescent.UnitNormBounds.sum_padicVal_shift_eq_factorial (l : ℕ) [Fact l.Prime] (mB : ℤ) (n : ℕ) :
    ∑ ct ∈ Finset.Ioo mB (mB + 1 + (n : ℤ)), vl l (ct - mB) = padicValNat l n.factorial := by sorry
