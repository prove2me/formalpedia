-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_T_mul
-- name    : Formalism.CohomologicalDescent.LA.la_T_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:49:33.184683+00:00
-- url     : https://prove2.me/theorems/0a8f3091-4d53-4fae-86be-781f01e46242
-- title:
--   LA: la T mul
-- statement:
--   The LA construction uses the la T mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L805-L812
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L805-L812

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

theorem Formalism.CohomologicalDescent.LA.la_T_mul {c d c' d' : ℕ} {f f' : MvPolynomial (Fin 2 × Fin 2) ℤ} (hf : f ∈ detPowMulMonomialSpan c d)
    (hf' : f' ∈ detPowMulMonomialSpan c' d') : f * f' ∈ detPowMulMonomialSpan (c + c') (d + d') := by sorry
