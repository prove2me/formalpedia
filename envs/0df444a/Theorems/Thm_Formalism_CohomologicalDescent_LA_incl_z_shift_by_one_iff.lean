-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_incl_z_shift_by_one_iff
-- name    : Formalism.CohomologicalDescent.LA.incl_z_shift_by_one_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:58:03.178043+00:00
-- url     : https://prove2.me/theorems/8c2f63bb-6437-462b-a74b-714d53e4e1a6
-- title:
--   LA: incl z shift by one iff
-- statement:
--   The LA construction uses the incl z shift by one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L409-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L409-L431

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

theorem Formalism.CohomologicalDescent.LA.incl_z_shift_by_one_iff (r : ℕ) (ν : Fin r → ℕ) (l e : ℕ) (hν : Antitone ν) :
    InclZ r r le_rfl (fun a => ν a + 1) l e ↔ InclZ r r le_rfl ν l e := by sorry
