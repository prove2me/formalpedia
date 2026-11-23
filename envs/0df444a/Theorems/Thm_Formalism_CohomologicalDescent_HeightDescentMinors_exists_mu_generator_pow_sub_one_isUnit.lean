-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_mu_generator_pow_sub_one_isUnit
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.exists_mu_generator_pow_sub_one_isUnit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:13.693137+00:00
-- url     : https://prove2.me/theorems/620b432a-8f65-4473-b7eb-f24a885d5e45
-- title:
--   Height Descent Minors: exists mu generator pow sub one is Unit
-- statement:
--   The Height Descent Minors construction uses the exists mu generator pow sub one is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1037-L1047
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1037-L1047

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.exists_mu_generator_pow_sub_one_isUnit (hm : MuFacts) : ∃ d ∈ mu l, ∀ j, 0 < j → j < l - 1 → IsUnit (d ^ j - 1) := by sorry
