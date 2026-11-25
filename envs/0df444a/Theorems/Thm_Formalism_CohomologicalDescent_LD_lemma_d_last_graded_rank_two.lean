-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_lemma_d_last_graded_rank_two
-- name    : Formalism.CohomologicalDescent.LD.lemma_d_last_graded_rank_two
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:23:42.578726+00:00
-- url     : https://prove2.me/theorems/b1d2fc63-f5e5-4eb2-a80b-19ad4e209616
-- title:
--   LD: lemma d last graded rank two
-- statement:
--   The LD construction uses the lemma d last graded rank two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L389-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L389-L389

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

theorem Formalism.CohomologicalDescent.LD.lemma_d_last_graded_rank_two : LemmaDLastGraded_rank2 := by sorry
