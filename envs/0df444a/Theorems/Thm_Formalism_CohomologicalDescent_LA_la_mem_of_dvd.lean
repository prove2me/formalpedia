-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_mem_of_dvd
-- name    : Formalism.CohomologicalDescent.LA.la_mem_of_dvd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:49:29.687439+00:00
-- url     : https://prove2.me/theorems/4136a09c-b91f-49fb-b2b1-6c153f034837
-- title:
--   LA: la mem of dvd
-- statement:
--   The LA construction uses the la mem of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L160-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L160-L169

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

theorem Formalism.CohomologicalDescent.LA.la_mem_of_dvd (R : Type) [CommRing R] {n : ℕ} (s : Fin n) {d p q N : ℕ} (h : p + q = d)
    (hN : (p + q).choose q ∣ N) :
    (N : MvPolynomial (Fin 2 × Fin n) R) * la_xy R s p q ∈ la_binLat R s d := by sorry
