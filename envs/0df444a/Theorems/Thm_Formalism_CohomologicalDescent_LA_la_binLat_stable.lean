-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_binLat_stable
-- name    : Formalism.CohomologicalDescent.LA.la_binLat_stable
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:49:54.708498+00:00
-- url     : https://prove2.me/theorems/bb31a2a8-ca5f-432e-b30f-e0736f9315b9
-- title:
--   LA: la bin Lat stable
-- statement:
--   The LA construction uses the la bin Lat stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L248-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L248-L316

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

theorem Formalism.CohomologicalDescent.LA.la_binLat_stable (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (d : ℕ) (a b : Fin 2) (k : ℕ)
    (f : MvPolynomial (Fin 2 × Fin n) R) (hf : f ∈ la_binLat R s d) :
    rowDiv R a b k f ∈ la_binLat R s d := by sorry
