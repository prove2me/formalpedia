-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r2_basis_holds
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.r2_basis_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:30.411878+00:00
-- url     : https://prove2.me/theorems/067688ba-12a8-45e4-81f1-7c0026fec93b
-- title:
--   Height Descent Minors: r2 basis holds
-- statement:
--   The Height Descent Minors construction uses the r2 basis holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1930-L1930
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1930-L1930

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.r2_basis_holds : PowerSeriesFreeBasis := by sorry
