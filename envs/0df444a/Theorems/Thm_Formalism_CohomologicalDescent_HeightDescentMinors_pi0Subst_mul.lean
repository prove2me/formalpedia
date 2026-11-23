-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_pi0Subst_mul
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.pi0Subst_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:22.2298+00:00
-- url     : https://prove2.me/theorems/51e21786-dc2b-4598-bfe0-0c6589d0ad10
-- title:
--   Height Descent Minors: pi0 Subst mul
-- statement:
--   The Height Descent Minors construction uses the pi0 Subst mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1013-L1014
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1013-L1014

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.pi0Subst_mul (f g : O⟦X⟧) : inc l O (f * g) = inc l O f * inc l O g := by sorry
