-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_lemma_d_graded_rank_two
-- name    : Formalism.CohomologicalDescent.LD.lemma_d_graded_rank_two
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:22:20.780134+00:00
-- url     : https://prove2.me/theorems/213d6450-db78-4a98-a172-237aa208c48c
-- title:
--   LD: lemma d graded rank two
-- statement:
--   The LD construction uses the lemma d graded rank two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L1070-L1070
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L1070-L1070

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
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

theorem Formalism.CohomologicalDescent.LD.lemma_d_graded_rank_two : LemmaDGraded_rank2 := by sorry
