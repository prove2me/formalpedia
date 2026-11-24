-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_weyl_r2n1
-- name    : Formalism.CohomologicalDescent.LA.la_weyl_r2n1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:49:40.474795+00:00
-- url     : https://prove2.me/theorems/726edf8a-d845-43fa-b5d2-3373bbc7de4d
-- title:
--   LA: la weyl r2n1
-- statement:
--   The LA construction uses the la weyl r2n1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L460-L478
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L460-L478

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

theorem Formalism.CohomologicalDescent.LA.la_weyl_r2n1 (R : Type) [CommRing R] (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) :
    weyl R 2 1 hn ν = la_binLat R (0 : Fin 1) (ν 0) := by sorry
