-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_inc
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.constantCoeff_inc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:48.245306+00:00
-- url     : https://prove2.me/theorems/a8bd796d-1bf5-4eb2-95d2-f53d41acc93e
-- title:
--   Height Descent Minors: constant Coeff inc
-- statement:
--   The Height Descent Minors construction uses the constant Coeff inc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1177-L1182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1177-L1182

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.constantCoeff_inc (hm : MuFacts) (f : O⟦X⟧) : constantCoeff (inc l O f) = constantCoeff f := by sorry
