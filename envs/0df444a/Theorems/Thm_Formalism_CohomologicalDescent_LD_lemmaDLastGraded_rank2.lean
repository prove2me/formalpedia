-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_lemmaDLastGraded_rank2
-- name    : Formalism.CohomologicalDescent.LD.lemmaDLastGraded_rank2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:51:04.482958+00:00
-- url     : https://prove2.me/theorems/524cba86-a66d-4b9a-b974-36c15dbbe939
-- title:
--   LD: lemma DLast Graded rank2
-- statement:
--   The LD construction uses the lemma DLast Graded rank2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L263-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L263-L290

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

theorem Formalism.CohomologicalDescent.LD.lemmaDLastGraded_rank2 : LemmaDLastGraded_rank2 := by sorry
