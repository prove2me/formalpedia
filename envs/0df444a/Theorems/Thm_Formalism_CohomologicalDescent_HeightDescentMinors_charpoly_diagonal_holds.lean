-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_charpoly_diagonal_holds
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.charpoly_diagonal_holds
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:37:22.407205+00:00
-- url     : https://prove2.me/theorems/92abc0bd-510b-4855-a25a-d6feab27fe26
-- title:
--   Height Descent Minors: charpoly diagonal holds
-- statement:
--   The Height Descent Minors construction uses the charpoly diagonal holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1395-L1416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1395-L1416

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.charpoly_diagonal_holds : CharpolyDiag := by sorry
