-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_phi_padic
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.map_phi_padic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:01.409543+00:00
-- url     : https://prove2.me/theorems/8ca847da-d1fe-4695-be38-c2785ea16189
-- title:
--   Height Descent Minors: map phi padic
-- statement:
--   The Height Descent Minors construction uses the map phi padic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L495-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L495-L499

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.map_phi_padic (f : ℤ_[l]⟦X⟧) :
    PowerSeries.map (algebraMap ℤ_[l] O) (phi l ℤ_[l] f) =
      phi l O (PowerSeries.map (algebraMap ℤ_[l] O) f) := by sorry
