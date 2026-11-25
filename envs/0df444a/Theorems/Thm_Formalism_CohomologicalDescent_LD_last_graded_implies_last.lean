-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_last_graded_implies_last
-- name    : Formalism.CohomologicalDescent.LD.last_graded_implies_last
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:21:28.400502+00:00
-- url     : https://prove2.me/theorems/fbd738c6-5dcf-5de0-b4db-26d3bcf9579b
-- title:
--   LD: last graded implies last
-- statement:
--   The LD construction uses the last graded implies last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L382-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L382-L382

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility

theorem Formalism.CohomologicalDescent.LD.last_graded_implies_last : LastGradedImpliesLast := by sorry
