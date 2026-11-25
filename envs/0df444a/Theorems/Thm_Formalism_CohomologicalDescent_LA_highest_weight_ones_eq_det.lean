-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_highest_weight_ones_eq_det
-- name    : Formalism.CohomologicalDescent.LA.highest_weight_ones_eq_det
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:21:56.494455+00:00
-- url     : https://prove2.me/theorems/c0441e3f-c99c-40cc-ac27-ecf2f39577cb
-- title:
--   LA: highest weight ones eq det
-- statement:
--   The LA construction uses the highest weight ones eq det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L139-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L139-L143

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility

theorem Formalism.CohomologicalDescent.LA.highest_weight_ones_eq_det (R : Type) [CommRing R] (r : ℕ) :
    hw R le_rfl (fun _ : Fin r => 1) = genericDet R r := by sorry
