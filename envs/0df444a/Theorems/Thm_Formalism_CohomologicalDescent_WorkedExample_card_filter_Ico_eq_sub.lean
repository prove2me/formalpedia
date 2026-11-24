-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_card_filter_Ico_eq_sub
-- name    : Formalism.CohomologicalDescent.WorkedExample.card_filter_Ico_eq_sub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:01:22.076903+00:00
-- url     : https://prove2.me/theorems/264a2463-ecfb-483b-a33b-394625606bd6
-- title:
--   Worked Example: card filter Ico eq sub
-- statement:
--   The Worked Example construction uses the card filter Ico eq sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L238-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L238-L250

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

theorem Formalism.CohomologicalDescent.WorkedExample.card_filter_Ico_eq_sub (N x y : ℕ) (hy : y ≤ N) :
    (Finset.univ.filter (fun a : Fin N => x ≤ (a : ℕ) ∧ (a : ℕ) < y)).card = y - x := by sorry
