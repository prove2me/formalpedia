-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_mem_mu_iff_pow_eq_one
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.mem_mu_iff_pow_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:28:04.728719+00:00
-- url     : https://prove2.me/theorems/f089e638-190b-421d-b408-631247d8a241
-- title:
--   Height Descent Minors: mem mu iff pow eq one
-- statement:
--   The Height Descent Minors construction uses the mem mu iff pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L221-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L221-L222

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
variable (l : ℕ) [Fact l.Prime]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.mem_mu_iff_pow_eq_one {d : ℤ_[l]} : d ∈ mu l ↔ d ^ (l - 1) = 1 := by sorry
