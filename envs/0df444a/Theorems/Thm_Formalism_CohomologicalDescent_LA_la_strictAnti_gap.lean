-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_strictAnti_gap
-- name    : Formalism.CohomologicalDescent.LA.la_strictAnti_gap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:23.173345+00:00
-- url     : https://prove2.me/theorems/1500a1e5-1a81-4890-bf0c-4e19e0136ed8
-- title:
--   LA: la strict Anti gap
-- statement:
--   The LA construction uses the la strict Anti gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L66-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L66-L83

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

theorem Formalism.CohomologicalDescent.LA.la_strictAnti_gap {r : ℕ} (U : Fin r → ℤ) (hU : StrictAnti U) :
    ∀ (k : ℕ) (a b : Fin r), b.val = a.val + k → U b + k ≤ U a := by sorry
