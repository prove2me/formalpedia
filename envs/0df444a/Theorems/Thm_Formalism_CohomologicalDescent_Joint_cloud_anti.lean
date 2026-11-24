-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_Joint_cloud_anti
-- name    : Formalism.CohomologicalDescent.Joint.cloud_anti
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:40:25.14087+00:00
-- url     : https://prove2.me/theorems/2425844a-fe38-4e51-beb5-90dcfdddaeca
-- title:
--   Joint: cloud anti
-- statement:
--   The Joint construction uses the cloud anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/JointExactExponentStopHigh.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/JointExactExponentStopHigh.lean#L13-L17

import Definitions.Def_Formalism_PieriBlockIdeals_StatementJ
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.Joint
open Formalism.RankGapBounds.ChebyshevFactorialBounds Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.Cor

theorem Formalism.CohomologicalDescent.Joint.cloud_anti {ι : Type} {D : Data ι} (W : Weights D) (τ : ι) : StrictAnti (W.cloud τ) := by sorry
