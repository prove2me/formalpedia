-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_X_pow_of_ne_zero
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.hasSubst_X_pow_of_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:04.551807+00:00
-- url     : https://prove2.me/theorems/ed0703d6-9d0f-4a44-bca5-65ff402d1d13
-- title:
--   Height Descent Minors: has Subst X pow of ne zero
-- statement:
--   The Height Descent Minors construction uses the has Subst X pow of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L465-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L465-L469

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.hasSubst_X_pow_of_ne_zero {R : Type} [CommRing R] {l : ℕ} (hl : l ≠ 0) :
    HasSubst (X ^ l : R⟦X⟧) := by sorry
