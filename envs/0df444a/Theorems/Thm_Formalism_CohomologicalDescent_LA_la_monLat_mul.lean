-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_monLat_mul
-- name    : Formalism.CohomologicalDescent.LA.la_monLat_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:49:27.641793+00:00
-- url     : https://prove2.me/theorems/7cb732ae-b2a3-42ca-aa50-d382ae1215e3
-- title:
--   LA: la mon Lat mul
-- statement:
--   The LA construction uses the la mon Lat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L792-L800
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L792-L800

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

theorem Formalism.CohomologicalDescent.LA.la_monLat_mul (R : Type) [CommRing R] {n : ℕ} (s : Fin n) {d d' : ℕ}
    {u u' : MvPolynomial (Fin 2 × Fin n) R} (hu : u ∈ la_monLat R s d)
    (hu' : u' ∈ la_monLat R s d') : u * u' ∈ la_monLat R s (d + d') := by sorry
