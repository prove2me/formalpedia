-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_example_b_div_lstar_eq
-- name    : Formalism.CohomologicalDescent.WorkedExample.example_b_div_lstar_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:17.984922+00:00
-- url     : https://prove2.me/theorems/77847538-c166-4db5-a136-6283c3442ccd
-- title:
--   Worked Example: example b div lstar eq
-- statement:
--   The Worked Example construction uses the example b div lstar eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L680-L683
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L680-L683

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

theorem Formalism.CohomologicalDescent.WorkedExample.example_b_div_lstar_eq : exampleParamsAlt.b / exampleParamsAlt.lstar = 1814470 := by sorry
