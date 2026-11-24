-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_coeff_binLat
-- name    : Formalism.CohomologicalDescent.LA.la_coeff_binLat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:10.371837+00:00
-- url     : https://prove2.me/theorems/c7a0d0d8-63ff-46e3-b2ec-1768ad6d96da
-- title:
--   LA: la coeff bin Lat
-- statement:
--   The LA construction uses the la coeff bin Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L331-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L331-L349

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

theorem Formalism.CohomologicalDescent.LA.la_coeff_binLat {n : ℕ} (s : Fin n) (d : ℕ) (f : MvPolynomial (Fin 2 × Fin n) ℤ)
    (hf : f ∈ la_binLat ℤ s d) (p q : ℕ) :
    ((p + q).choose q : ℤ) ∣ coeff (la_mono s p q) f := by sorry
