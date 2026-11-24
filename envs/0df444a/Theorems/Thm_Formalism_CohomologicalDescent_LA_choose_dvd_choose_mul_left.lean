-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_choose_dvd_choose_mul_left
-- name    : Formalism.CohomologicalDescent.LA.choose_dvd_choose_mul_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:49:41.82387+00:00
-- url     : https://prove2.me/theorems/da6039f8-34a1-4601-bbb1-3bae648ef1cb
-- title:
--   LA: choose dvd choose mul left
-- statement:
--   The LA construction uses the choose dvd choose mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L237-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L237-L243

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

theorem Formalism.CohomologicalDescent.LA.choose_dvd_choose_mul_left (p k q : ℕ) :
    (p + k + q).choose q ∣ (p + (q + k)).choose (q + k) * (q + k).choose k := by sorry
