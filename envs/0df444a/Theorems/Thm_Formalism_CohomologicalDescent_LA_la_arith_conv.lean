-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_arith_conv
-- name    : Formalism.CohomologicalDescent.LA.la_arith_conv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:49:52.231367+00:00
-- url     : https://prove2.me/theorems/acb1e269-c8e2-423b-a869-eeb2a63ecd35
-- title:
--   LA: la arith conv
-- statement:
--   The LA construction uses the la arith conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L369-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L369-L384

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

theorem Formalism.CohomologicalDescent.LA.la_arith_conv (l d m e : ℕ) (hl : l.Prime) (hm : ¬ l ∣ m)
    (h : ∀ i ≤ d, d.choose i ∣ m * l ^ e) : Formalism.RankGapBounds.JumpSetsAlt.maxVal l d ≤ e := by sorry
