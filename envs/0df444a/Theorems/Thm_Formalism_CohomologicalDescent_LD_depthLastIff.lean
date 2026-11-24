-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_depthLastIff
-- name    : Formalism.CohomologicalDescent.LD.depthLastIff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:52:36.956261+00:00
-- url     : https://prove2.me/theorems/05012b4d-26a8-4a3f-b385-794f5624e1a8
-- title:
--   LD: depth Last Iff
-- statement:
--   The LD construction uses the depth Last Iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L38-L43

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

theorem Formalism.CohomologicalDescent.LD.depthLastIff : DepthLastIff := by sorry
