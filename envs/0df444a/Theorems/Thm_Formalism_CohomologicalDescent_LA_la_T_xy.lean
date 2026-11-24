-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_T_xy
-- name    : Formalism.CohomologicalDescent.LA.la_T_xy
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:49:10.624804+00:00
-- url     : https://prove2.me/theorems/14e8c47d-6dd6-4863-ad23-b6fe2397e803
-- title:
--   LA: la T xy
-- statement:
--   The LA construction uses the la T xy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L814-L816
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L814-L816

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

theorem Formalism.CohomologicalDescent.LA.la_T_xy (c p q : ℕ) : la_det ℤ ^ c * la_xy ℤ (0 : Fin 2) p q ∈ detPowMulMonomialSpan c (p + q) := by sorry
