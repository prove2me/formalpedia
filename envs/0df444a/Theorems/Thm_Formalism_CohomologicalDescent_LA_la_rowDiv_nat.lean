-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowDiv_nat
-- name    : Formalism.CohomologicalDescent.LA.la_rowDiv_nat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:41.806193+00:00
-- url     : https://prove2.me/theorems/7e290c3e-a12f-4f99-8239-0af36742f059
-- title:
--   LA: la row Div nat
-- statement:
--   The LA construction uses the la row Div nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L223-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L223-L228

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

theorem Formalism.CohomologicalDescent.LA.la_rowDiv_nat (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k N : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k ((N : MvPolynomial (Fin r × Fin n) R) * f) =
      (N : MvPolynomial (Fin r × Fin n) R) * rowDiv R a b k f := by sorry
