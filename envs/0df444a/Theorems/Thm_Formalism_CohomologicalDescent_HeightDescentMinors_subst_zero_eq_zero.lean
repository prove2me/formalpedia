-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_subst_zero_eq_zero
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.subst_zero_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:35.013456+00:00
-- url     : https://prove2.me/theorems/15e7a3b7-7ea5-4e1b-9f0e-767e2c5d16a9
-- title:
--   Height Descent Minors: subst zero eq zero
-- statement:
--   The Height Descent Minors construction uses the subst zero eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L744-L745
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L744-L745

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
variable {R : Type} [CommRing R]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.subst_zero_eq_zero {a : R⟦X⟧} (ha : HasSubst a) : (0 : R⟦X⟧).subst a = 0 := by sorry
