-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_rank_two_vector_weighted_homog
-- name    : Formalism.CohomologicalDescent.LD.rank_two_vector_weighted_homog
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:40:42.606316+00:00
-- url     : https://prove2.me/theorems/985998a9-e245-4c31-8afc-53c8b3007385
-- title:
--   LD: rank two vector weighted homog
-- statement:
--   The LD construction uses the rank two vector weighted homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L223-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L223-L237

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

theorem Formalism.CohomologicalDescent.LD.rank_two_vector_weighted_homog (w y i : ℕ) (h : y + i ≤ w) :
    IsWeightedHomogeneous (rowW 2 2) (vec2 w y i) (wt2 (w - i) (y + i)) := by sorry
