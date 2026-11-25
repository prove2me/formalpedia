-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_xy_mem_binLat
-- name    : Formalism.CohomologicalDescent.LA.la_xy_mem_binLat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:22:10.351312+00:00
-- url     : https://prove2.me/theorems/59fe0426-b228-495a-ae2c-2efff2f444a3
-- title:
--   LA: la xy mem bin Lat
-- statement:
--   The LA construction uses the la xy mem bin Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L763-L766
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L763-L766

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

theorem Formalism.CohomologicalDescent.LA.la_xy_mem_binLat (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (d : ℕ) :
    la_xy R s d 0 ∈ la_binLat R s d := by sorry
