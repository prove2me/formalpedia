-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_prod_comp_eq_prod_comp
-- name    : Formalism.CohomologicalDescent.WorkedExample.prod_comp_eq_prod_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:42.843707+00:00
-- url     : https://prove2.me/theorems/bf172289-1e84-4e6e-adb2-b7bf9dba16ad
-- title:
--   Worked Example: prod comp eq prod comp
-- statement:
--   The Worked Example construction uses the prod comp eq prod comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L57-L59

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

theorem Formalism.CohomologicalDescent.WorkedExample.prod_comp_eq_prod_comp {K : Type} [CommRing K] {N : ℕ} (f : Fin N → Polynomial K) (g : Polynomial K) :
    (∏ a, f a).comp g = ∏ a, (f a).comp g := by sorry
