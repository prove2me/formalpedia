-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_mono_of_weight
-- name    : Formalism.CohomologicalDescent.LA.la_mono_of_weight
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:49:33.988947+00:00
-- url     : https://prove2.me/theorems/b77f9b38-87ac-487a-b43f-016a48747962
-- title:
--   LA: la mono of weight
-- statement:
--   The LA construction uses the la mono of weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L480-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L480-L488

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

theorem Formalism.CohomologicalDescent.LA.la_mono_of_weight {m : Fin 2 × Fin 1 →₀ ℕ} {ν : Fin 1 → ℕ}
    (h : Finsupp.weight (colW 2 1) m = ν) :
    m = la_mono (0 : Fin 1) (m (0, 0)) (m (1, 0)) ∧ m (0, 0) + m (1, 0) = ν 0 := by sorry
