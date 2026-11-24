-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_tw_stable
-- name    : Formalism.CohomologicalDescent.LA.la_tw_stable
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:36.26681+00:00
-- url     : https://prove2.me/theorems/2b07512f-0772-4441-a321-50317a79bce3
-- title:
--   LA: la tw stable
-- statement:
--   The LA construction uses the la tw stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L747-L761
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L747-L761

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

theorem Formalism.CohomologicalDescent.LA.la_tw_stable (R : Type) [CommRing R] (L : Submodule R (MvPolynomial (Fin 2 × Fin 2) R))
    (hs : ∀ (a b : Fin 2) (k : ℕ) (f : MvPolynomial (Fin 2 × Fin 2) R), f ∈ L →
      rowDiv R a b k f ∈ L) (c : ℕ) (a b : Fin 2) (k : ℕ) (f : MvPolynomial (Fin 2 × Fin 2) R)
    (hf : f ∈ L.map (LinearMap.mulLeft R (la_det R ^ c))) :
    rowDiv R a b k f ∈ L.map (LinearMap.mulLeft R (la_det R ^ c)) := by sorry
