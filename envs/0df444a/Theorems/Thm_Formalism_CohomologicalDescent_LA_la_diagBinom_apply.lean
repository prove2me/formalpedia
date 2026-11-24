-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_diagBinom_apply
-- name    : Formalism.CohomologicalDescent.LA.la_diagBinom_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:49:57.652663+00:00
-- url     : https://prove2.me/theorems/bec9f1a8-36d6-4b41-bfb9-adbf5e27194a
-- title:
--   LA: la diag Binom apply
-- statement:
--   The LA construction uses the la diag Binom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L565-L567
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L565-L567

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

theorem Formalism.CohomologicalDescent.LA.la_diagBinom_apply (R : Type) [CommRing R] (d : ℕ) (c : Fin (d + 1) → R) (i : Fin (d + 1)) :
    Formalism.CohomologicalDescent.diagBinom R d c i = (d.choose i.val : R) * c i := by sorry
