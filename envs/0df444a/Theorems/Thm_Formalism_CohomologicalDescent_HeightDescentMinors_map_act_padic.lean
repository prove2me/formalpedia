-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_act_padic
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.map_act_padic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:59.895496+00:00
-- url     : https://prove2.me/theorems/efacb5b3-989b-4929-a40e-fb155c058eff
-- title:
--   Height Descent Minors: map act padic
-- statement:
--   The Height Descent Minors construction uses the map act padic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1204-L1207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1204-L1207

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.map_act_padic (c : ℤ_[l]) (f : ℤ_[l]⟦X⟧) :
    PowerSeries.map (algebraMap ℤ_[l] O) (act l ℤ_[l] c f) =
      act l O c (PowerSeries.map (algebraMap ℤ_[l] O) f) := by sorry
