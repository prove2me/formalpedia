-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_incl_R_of_Z
-- name    : Formalism.CohomologicalDescent.LA.la_incl_R_of_Z
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:50:16.114234+00:00
-- url     : https://prove2.me/theorems/2af83fdd-981f-4e64-aa5a-1bef1de0a6fb
-- title:
--   LA: la incl R of Z
-- statement:
--   The LA construction uses the la incl R of Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L1068-L1090
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L1068-L1090

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

theorem Formalism.CohomologicalDescent.LA.la_incl_R_of_Z (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ)
    (l e : ℕ) (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) (hZ : InclZ r n hn ν l e)
    (x : MvPolynomial (Fin r × Fin n) R) (hx : x ∈ dualWeyl R r n ν) :
    (l : R) ^ e • x ∈ weyl R r n hn ν := by sorry
