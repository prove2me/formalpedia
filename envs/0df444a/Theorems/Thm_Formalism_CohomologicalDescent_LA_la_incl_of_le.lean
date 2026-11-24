-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_incl_of_le
-- name    : Formalism.CohomologicalDescent.LA.la_incl_of_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:49:55.937805+00:00
-- url     : https://prove2.me/theorems/1506ee64-7fba-474e-bce6-d2323f274b42
-- title:
--   LA: la incl of le
-- statement:
--   The LA construction uses the la incl of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L129-L132

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

theorem Formalism.CohomologicalDescent.LA.la_incl_of_le {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (l e : ℕ) (hl : l.Prime)
    (h : dualWeyl ℤ r n ν ≤ weyl ℤ r n hn ν) : InclZ r n hn ν l e := by sorry
