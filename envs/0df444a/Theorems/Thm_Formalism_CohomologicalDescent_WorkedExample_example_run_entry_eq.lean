-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_example_run_entry_eq
-- name    : Formalism.CohomologicalDescent.WorkedExample.example_run_entry_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:15.500044+00:00
-- url     : https://prove2.me/theorems/3e673610-16e0-42d7-9ceb-76e11c5d684f
-- title:
--   Worked Example: example run entry eq
-- statement:
--   The Worked Example construction uses the example run entry eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L311-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L311-L315

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

theorem Formalism.CohomologicalDescent.WorkedExample.example_run_entry_eq (p q' t : ℕ) (v : Fin p → ℝ) (β : Fin q' → ℝ) (e : ℝ) (a : Fin t) :
    exampleParameterVector p q' t v β e (Fin.castAdd q' (Fin.natAdd p a)) =
      -e + ((t : ℝ) - 1) / 2 - ((a : ℕ) : ℝ) := by sorry
