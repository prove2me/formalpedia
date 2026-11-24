-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_exZ_le_of_U
-- name    : Formalism.CohomologicalDescent.LA.la_exZ_le_of_U
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:49:41.762559+00:00
-- url     : https://prove2.me/theorems/9686e193-885e-48d1-9f64-6f311aad3fca
-- title:
--   LA: la ex Z le of U
-- statement:
--   The LA construction uses the la ex Z le of U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L1227-L1231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L1227-L1231

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

theorem Formalism.CohomologicalDescent.LA.la_exZ_le_of_U (hA : LemmaAZ) (r : ℕ) (U : Fin r → ℤ) (hU : StrictAnti U) (h0 : ∀ a, 0 ≤ U a)
    (l : ℕ) (hl : l.Prime) : exZ r r le_rfl (nuOf U) l ≤ Formalism.RankGapBounds.JumpSetsAlt.eExp U l := by sorry
