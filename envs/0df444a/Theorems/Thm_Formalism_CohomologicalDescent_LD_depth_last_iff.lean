-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_depth_last_iff
-- name    : Formalism.CohomologicalDescent.LD.depth_last_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:22:25.911138+00:00
-- url     : https://prove2.me/theorems/ed0076c7-0df0-478c-af9b-09032b6e7a66
-- title:
--   LD: depth last iff
-- statement:
--   The LD construction uses the depth last iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L385-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L385-L385

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

theorem Formalism.CohomologicalDescent.LD.depth_last_iff : DepthLastIff := by sorry
