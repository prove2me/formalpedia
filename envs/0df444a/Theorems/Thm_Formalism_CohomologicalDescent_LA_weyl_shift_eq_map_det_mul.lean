-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_weyl_shift_eq_map_det_mul
-- name    : Formalism.CohomologicalDescent.LA.weyl_shift_eq_map_det_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:59:53.156954+00:00
-- url     : https://prove2.me/theorems/e3e64671-f398-4eb0-ab34-9cf44ca32b68
-- title:
--   LA: weyl shift eq map det mul
-- statement:
--   The LA construction uses the weyl shift eq map det mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L186-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L186-L204

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

theorem Formalism.CohomologicalDescent.LA.weyl_shift_eq_map_det_mul (R : Type) [CommRing R] {r : ℕ} (ν : Fin r → ℕ) :
    weyl R r r le_rfl (fun a => ν a + 1) =
      (weyl R r r le_rfl ν).map (LinearMap.mulLeft R (genericDet R r)) := by sorry
