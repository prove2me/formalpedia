-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_prod_initial_minors_mem_det_span
-- name    : Formalism.CohomologicalDescent.LA.prod_initial_minors_mem_det_span
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:06.384366+00:00
-- url     : https://prove2.me/theorems/51aa294a-ce59-4597-8d97-e9bfeb7d7c29
-- title:
--   LA: prod initial minors mem det span
-- statement:
--   The LA construction uses the prod initial minors mem det span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L854-L864
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L854-L864

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

theorem Formalism.CohomologicalDescent.LA.prod_initial_minors_mem_det_span {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ 2) (I : ∀ k, Fin (sz k) → Fin 2)
    (S : Finset (Fin K)) :
    ∏ k ∈ S, initMinor ℤ (I k) (hsz k) ∈
      detPowMulMonomialSpan (∑ k ∈ S, if sz k = 2 then 1 else 0) (∑ k ∈ S, if sz k = 1 then 1 else 0) := by sorry
