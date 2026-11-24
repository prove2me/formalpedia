-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_leading_minor_full_eq_det
-- name    : Formalism.CohomologicalDescent.LA.leading_minor_full_eq_det
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:59:08.116241+00:00
-- url     : https://prove2.me/theorems/bd85aac8-28e2-4b1f-8e94-4059b80c5ec4
-- title:
--   LA: leading minor full eq det
-- statement:
--   The LA construction uses the leading minor full eq det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L19-L22

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

theorem Formalism.CohomologicalDescent.LA.leading_minor_full_eq_det (R : Type) [CommRing R] {r : ℕ} (s : ℕ) (hs : s = r) (hr : s ≤ r)
    (hn : s ≤ r) : lpMinor R s hr hn = genericDet R r := by sorry
