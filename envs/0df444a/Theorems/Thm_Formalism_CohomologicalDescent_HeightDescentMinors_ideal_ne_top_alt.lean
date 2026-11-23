-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_ideal_ne_top_alt
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.ideal_ne_top_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:55.800082+00:00
-- url     : https://prove2.me/theorems/c0b1bc6c-b47e-4af3-a723-ca0dbf539635
-- title:
--   Height Descent Minors: ideal ne top alt
-- statement:
--   The Height Descent Minors construction uses the ideal ne top alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1670-L1674
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1670-L1674

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.ideal_ne_top_alt : I ≠ ⊤ := by sorry
