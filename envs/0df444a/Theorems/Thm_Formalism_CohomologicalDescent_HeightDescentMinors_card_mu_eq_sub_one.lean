-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_card_mu_eq_sub_one
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.card_mu_eq_sub_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:40.664587+00:00
-- url     : https://prove2.me/theorems/f2e88851-fdd1-4dcc-a5dc-14aa3814ab1c
-- title:
--   Height Descent Minors: card mu eq sub one
-- statement:
--   The Height Descent Minors construction uses the card mu eq sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L279-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L279-L281

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable (l : ℕ) [Fact l.Prime]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.card_mu_eq_sub_one : (mu l).card = l - 1 := by sorry
