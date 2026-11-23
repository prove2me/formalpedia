-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_X_sub_C_isDistinguished
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.X_sub_C_isDistinguished
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:34.504181+00:00
-- url     : https://prove2.me/theorems/063697c9-e03d-453a-9a6b-97807d6b98bf
-- title:
--   Height Descent Minors: X sub C is Distinguished
-- statement:
--   The Height Descent Minors construction uses the X sub C is Distinguished property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1660-L1665
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1660-L1665

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.X_sub_C_isDistinguished (hc : c ∈ I) :
    (Polynomial.X - Polynomial.C c : Polynomial O).IsDistinguishedAt I := by sorry
