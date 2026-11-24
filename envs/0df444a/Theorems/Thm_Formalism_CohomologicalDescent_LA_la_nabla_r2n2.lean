-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_nabla_r2n2
-- name    : Formalism.CohomologicalDescent.LA.la_nabla_r2n2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:50:03.247063+00:00
-- url     : https://prove2.me/theorems/38deade3-bf1b-4c23-9ea8-338608d82fbc
-- title:
--   LA: la nabla r2n2
-- statement:
--   The LA construction uses the la nabla r2n2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L872-L915
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L872-L915

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

theorem Formalism.CohomologicalDescent.LA.la_nabla_r2n2 (hn : 2 ≤ 2) (ν : Fin 2 → ℕ) (hν : Antitone ν) :
    dualWeyl ℤ 2 2 ν = detPowMulMonomialSpan (ν 1) (ν 0 - ν 1) := by sorry
