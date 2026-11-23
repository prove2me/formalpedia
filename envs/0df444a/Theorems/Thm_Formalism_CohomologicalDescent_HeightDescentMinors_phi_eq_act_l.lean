-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_phi_eq_act_l
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.phi_eq_act_l
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:19.394886+00:00
-- url     : https://prove2.me/theorems/597a15a1-f8e4-47a6-9873-29123cb34c7b
-- title:
--   Height Descent Minors: phi eq act l
-- statement:
--   The Height Descent Minors construction uses the phi eq act l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L160-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L160-L161

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.phi_eq_act_l (f : O⟦X⟧) : phi l O f = act l O (l : ℤ_[l]) f := by sorry
