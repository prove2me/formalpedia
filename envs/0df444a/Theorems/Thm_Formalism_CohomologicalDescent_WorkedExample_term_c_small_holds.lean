-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_term_c_small_holds
-- name    : Formalism.CohomologicalDescent.WorkedExample.term_c_small_holds
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:22:49.106874+00:00
-- url     : https://prove2.me/theorems/b1a9b381-3c46-40c4-8241-361c052337ee
-- title:
--   Worked Example: term c small holds
-- statement:
--   The Worked Example construction uses the term c small holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L716-L726
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L716-L726

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent

theorem Formalism.CohomologicalDescent.WorkedExample.term_c_small_holds : TermCSmall := by sorry
