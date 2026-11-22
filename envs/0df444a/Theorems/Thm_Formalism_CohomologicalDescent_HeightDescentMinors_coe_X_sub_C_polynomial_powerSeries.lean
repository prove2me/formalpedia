-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coe_X_sub_C_polynomial_powerSeries
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.coe_X_sub_C_polynomial_powerSeries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:50.914283+00:00
-- url     : https://prove2.me/theorems/fd9c388f-695a-426b-b60a-bdfc0db870e1
-- title:
--   Height Descent Minors: coe X sub C polynomial power Series
-- statement:
--   The Height Descent Minors construction uses the coe X sub C polynomial power Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1667-L1668
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1667-L1668

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
variable {O : Type} [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (c : O)

theorem Formalism.CohomologicalDescent.HeightDescentMinors.coe_X_sub_C_polynomial_powerSeries : ((Polynomial.X - Polynomial.C c : Polynomial O) : O⟦X⟧) = X - C c := by sorry
