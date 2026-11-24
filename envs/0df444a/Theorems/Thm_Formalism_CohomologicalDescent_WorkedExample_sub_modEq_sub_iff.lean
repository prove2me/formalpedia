-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_sub_modEq_sub_iff
-- name    : Formalism.CohomologicalDescent.WorkedExample.sub_modEq_sub_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:01:53.237804+00:00
-- url     : https://prove2.me/theorems/813c0d6a-3c48-4826-aeb3-c0afe1005593
-- title:
--   Worked Example: sub mod Eq sub iff
-- statement:
--   The Worked Example construction uses the sub mod Eq sub iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L28-L30

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

theorem Formalism.CohomologicalDescent.WorkedExample.sub_modEq_sub_iff (l : ℕ) (h x u : ℤ) :
    h - x ≡ h - u [ZMOD (l : ℤ)] ↔ x ≡ u [ZMOD (l : ℤ)] := by sorry
