-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_inc_X_sub_l_eq_q0
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.inc_X_sub_l_eq_q0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:58.193826+00:00
-- url     : https://prove2.me/theorems/57702f35-c985-46ed-884f-682fabdbb1a1
-- title:
--   Height Descent Minors: inc X sub l eq q0
-- statement:
--   The Height Descent Minors construction uses the inc X sub l eq q0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1022-L1030
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1022-L1030

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
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.inc_X_sub_l_eq_q0 : inc l O (X - C (l : O)) = q0 l O := by sorry
