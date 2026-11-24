-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_choose_dvd_choose_mul_right
-- name    : Formalism.CohomologicalDescent.LA.choose_dvd_choose_mul_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:49:58.084607+00:00
-- url     : https://prove2.me/theorems/f66cdbe1-c2ce-4de2-b562-4ba8e6e3188c
-- title:
--   LA: choose dvd choose mul right
-- statement:
--   The LA construction uses the choose dvd choose mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L230-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L230-L235

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
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

theorem Formalism.CohomologicalDescent.LA.choose_dvd_choose_mul_right (p k q : ℕ) :
    (p + (k + q)).choose (k + q) ∣ (p + k + q).choose q * (p + k).choose k := by sorry
