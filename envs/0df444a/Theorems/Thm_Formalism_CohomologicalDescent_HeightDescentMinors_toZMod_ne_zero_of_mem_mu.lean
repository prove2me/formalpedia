-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_ne_zero_of_mem_mu
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_ne_zero_of_mem_mu
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:17.034218+00:00
-- url     : https://prove2.me/theorems/091d7faf-547f-42ad-abb4-23a296c5ab42
-- title:
--   Height Descent Minors: to ZMod ne zero of mem mu
-- statement:
--   The Height Descent Minors construction uses the to ZMod ne zero of mem mu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L259-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L259-L264

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_ne_zero_of_mem_mu {d : ℤ_[l]} (hd : d ∈ mu l) : PadicInt.toZMod d ≠ 0 := by sorry
