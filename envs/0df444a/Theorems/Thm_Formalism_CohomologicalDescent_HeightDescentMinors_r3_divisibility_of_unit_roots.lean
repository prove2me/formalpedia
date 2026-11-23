-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r3_divisibility_of_unit_roots
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.r3_divisibility_of_unit_roots
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:30.444842+00:00
-- url     : https://prove2.me/theorems/14110a1d-1672-4b6f-8657-0dea1ef63b53
-- title:
--   Height Descent Minors: r3 divisibility of unit roots
-- statement:
--   The Height Descent Minors construction uses the r3 divisibility of unit roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L706-L714
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L706-L714

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.r3_divisibility_of_unit_roots (h3 : UnitFactorQ) (hr : QRoots) : RootOfUnityRemainder := by sorry
