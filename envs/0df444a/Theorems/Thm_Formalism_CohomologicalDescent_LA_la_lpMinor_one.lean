-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_lpMinor_one
-- name    : Formalism.CohomologicalDescent.LA.la_lpMinor_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:49:44.576834+00:00
-- url     : https://prove2.me/theorems/5991331d-fb0e-436b-ae92-8671445dcbf7
-- title:
--   LA: la lp Minor one
-- statement:
--   The LA construction uses the la lp Minor one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L434-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L434-L441

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

theorem Formalism.CohomologicalDescent.LA.la_lpMinor_one (R : Type) [CommRing R] {r n : ℕ} (s : ℕ) (hs : s = 1) (hr : s ≤ r)
    (hn : s ≤ n) :
    lpMinor R s hr hn = X ((⟨0, by omega⟩ : Fin r), (⟨0, by omega⟩ : Fin n)) := by sorry
