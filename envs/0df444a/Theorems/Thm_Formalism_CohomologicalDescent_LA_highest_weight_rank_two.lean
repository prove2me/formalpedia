-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_highest_weight_rank_two
-- name    : Formalism.CohomologicalDescent.LA.highest_weight_rank_two
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:49:25.033305+00:00
-- url     : https://prove2.me/theorems/d3ea1d58-65a1-41d2-85fd-d4a4497da741
-- title:
--   LA: highest weight rank two
-- statement:
--   The LA construction uses the highest weight rank two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L707-L715
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L707-L715

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

theorem Formalism.CohomologicalDescent.LA.highest_weight_rank_two (R : Type) [CommRing R] (hn : 2 ≤ 2) (ν : Fin 2 → ℕ) :
    hw R hn ν = la_det R ^ ν 1 * la_xy R (0 : Fin 2) (ν 0 - ν 1) 0 := by sorry
