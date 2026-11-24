-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_word_mem
-- name    : Formalism.CohomologicalDescent.LA.la_word_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:49:40.183008+00:00
-- url     : https://prove2.me/theorems/a4177fd6-e561-45fb-95f2-b0296320cf7c
-- title:
--   LA: la word mem
-- statement:
--   The LA construction uses the la word mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L123-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L123-L124

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

theorem Formalism.CohomologicalDescent.LA.la_word_mem (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (w : List (Fin r × Fin r × ℕ)) : applyWord R w (hw R hn ν) ∈ weyl R r n hn ν := by sorry
