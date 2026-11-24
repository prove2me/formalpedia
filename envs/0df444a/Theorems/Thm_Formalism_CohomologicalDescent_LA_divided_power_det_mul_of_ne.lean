-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_divided_power_det_mul_of_ne
-- name    : Formalism.CohomologicalDescent.LA.divided_power_det_mul_of_ne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:57:59.653799+00:00
-- url     : https://prove2.me/theorems/886ecc91-7557-4b3c-b1ea-f29a9d568614
-- title:
--   LA: divided power det mul of ne
-- statement:
--   The LA construction uses the divided power det mul of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L56-L60

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

theorem Formalism.CohomologicalDescent.LA.divided_power_det_mul_of_ne (R : Type) [CommRing R] {r : ℕ} (a b : Fin r) (hab : a ≠ b) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin r) R) :
    rowDiv R a b k (genericDet R r * f) = genericDet R r * rowDiv R a b k f := by sorry
