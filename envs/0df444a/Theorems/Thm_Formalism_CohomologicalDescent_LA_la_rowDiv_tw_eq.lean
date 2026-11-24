-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowDiv_tw_eq
-- name    : Formalism.CohomologicalDescent.LA.la_rowDiv_tw_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:50:54.607647+00:00
-- url     : https://prove2.me/theorems/9c27e2cc-5ad9-4e1e-9665-7ed56c23cae3
-- title:
--   LA: la row Div tw eq
-- statement:
--   The LA construction uses the la row Div tw eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L737-L745
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L737-L745

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

theorem Formalism.CohomologicalDescent.LA.la_rowDiv_tw_eq (R : Type) [CommRing R] (a : Fin 2) (k c : ℕ)
    (f : MvPolynomial (Fin 2 × Fin 2) R) :
    rowDiv R a a k (la_det R ^ c * f) = la_det R ^ c *
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, (c.choose x.1 : MvPolynomial (Fin 2 × Fin 2) R) *
        rowDiv R a a x.2 f := by sorry
