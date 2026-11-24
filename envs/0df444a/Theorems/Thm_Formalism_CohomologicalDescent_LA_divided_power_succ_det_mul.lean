-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_divided_power_succ_det_mul
-- name    : Formalism.CohomologicalDescent.LA.divided_power_succ_det_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:31.955338+00:00
-- url     : https://prove2.me/theorems/f7a54599-8c98-490b-929f-e38af8444991
-- title:
--   LA: divided power succ det mul
-- statement:
--   The LA construction uses the divided power succ det mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L69-L75

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

theorem Formalism.CohomologicalDescent.LA.divided_power_succ_det_mul (R : Type) [CommRing R] {r : ℕ} (a : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin r) R) :
    rowDiv R a a (k + 1) (genericDet R r * f) =
      genericDet R r * (rowDiv R a a (k + 1) f + rowDiv R a a k f) := by sorry
