-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_highest_weight_one_column
-- name    : Formalism.CohomologicalDescent.LA.highest_weight_one_column
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:50:08.261807+00:00
-- url     : https://prove2.me/theorems/7e00fbb5-4aa4-4761-bbf1-1c70eb46e33b
-- title:
--   LA: highest weight one column
-- statement:
--   The LA construction uses the highest weight one column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L443-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L443-L447

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

theorem Formalism.CohomologicalDescent.LA.highest_weight_one_column (R : Type) [CommRing R] {r : ℕ} (hn : 1 ≤ r) (ν : Fin 1 → ℕ) :
    hw R hn ν = X ((⟨0, hn⟩ : Fin r), (0 : Fin 1)) ^ ν 0 := by sorry
