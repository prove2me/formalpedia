-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_two_pow_sixty_le_example_b
-- name    : Formalism.CohomologicalDescent.WorkedExample.two_pow_sixty_le_example_b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:01.889769+00:00
-- url     : https://prove2.me/theorems/613392b1-11ea-4fd7-be17-47f110994e59
-- title:
--   Worked Example: two pow sixty le example b
-- statement:
--   The Worked Example construction uses the two pow sixty le example b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L671-L675
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L671-L675

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

theorem Formalism.CohomologicalDescent.WorkedExample.two_pow_sixty_le_example_b : (2 : ℝ) ^ 60 ≤ exampleParamsAlt.b := by sorry
