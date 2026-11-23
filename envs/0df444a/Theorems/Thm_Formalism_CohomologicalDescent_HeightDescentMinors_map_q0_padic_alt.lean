-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_q0_padic_alt
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.map_q0_padic_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:06.56802+00:00
-- url     : https://prove2.me/theorems/5cb3426b-4666-432a-b110-6dbbeb1ecdf8
-- title:
--   Height Descent Minors: map q0 padic alt
-- statement:
--   The Height Descent Minors construction uses the map q0 padic alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1202-L1202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1202-L1202

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.map_q0_padic_alt : PowerSeries.map (algebraMap ℤ_[l] O) (q0 l ℤ_[l]) = q0 l O := by sorry
