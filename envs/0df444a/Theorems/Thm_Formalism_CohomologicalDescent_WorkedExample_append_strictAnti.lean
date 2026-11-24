-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_append_strictAnti
-- name    : Formalism.CohomologicalDescent.WorkedExample.append_strictAnti
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:01:48.867552+00:00
-- url     : https://prove2.me/theorems/85b5a0d5-67fe-4fa9-802c-7922753a4b45
-- title:
--   Worked Example: append strict Anti
-- statement:
--   The Worked Example construction uses the append strict Anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L326-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L326-L350

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

theorem Formalism.CohomologicalDescent.WorkedExample.append_strictAnti {m n : ℕ} (f : Fin m → ℝ) (g : Fin n → ℝ) (hf : StrictAnti f)
    (hg : StrictAnti g) (hfg : ∀ i j, g j < f i) : StrictAnti (Fin.append f g) := by sorry
