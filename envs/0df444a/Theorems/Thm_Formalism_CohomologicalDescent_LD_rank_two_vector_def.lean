-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_rank_two_vector_def
-- name    : Formalism.CohomologicalDescent.LD.rank_two_vector_def
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:41:09.044953+00:00
-- url     : https://prove2.me/theorems/7fafb1d9-0830-4b96-b59a-64a5a0ec49b0
-- title:
--   LD: rank two vector def
-- statement:
--   The LD construction uses the rank two vector def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L190-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L190-L190

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

theorem Formalism.CohomologicalDescent.LD.rank_two_vector_def (w y i : ℕ) : vec2 w y i = X (0, 0) ^ (w - y - i) * X (1, 0) ^ i * ldDet ^ y := by sorry
