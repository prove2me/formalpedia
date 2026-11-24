-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_smul_monLat
-- name    : Formalism.CohomologicalDescent.LA.la_smul_monLat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:24.118833+00:00
-- url     : https://prove2.me/theorems/6d610dcb-7e5a-498e-9f3b-412786066f47
-- title:
--   LA: la smul mon Lat
-- statement:
--   The LA construction uses the la smul mon Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L386-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L386-L403

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

theorem Formalism.CohomologicalDescent.LA.la_smul_monLat {n : ℕ} (s : Fin n) (d N : ℕ) (hN : ∀ i ≤ d, d.choose i ∣ N)
    (y : MvPolynomial (Fin 2 × Fin n) ℤ) (hy : y ∈ la_monLat ℤ s d) :
    ((N : ℕ) : ℤ) • y ∈ la_binLat ℤ s d := by sorry
