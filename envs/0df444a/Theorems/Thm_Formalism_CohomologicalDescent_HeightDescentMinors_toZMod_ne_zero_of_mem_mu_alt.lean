-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_ne_zero_of_mem_mu_alt
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_ne_zero_of_mem_mu_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:39.027181+00:00
-- url     : https://prove2.me/theorems/c5d5f814-04cd-4305-be9e-bcb141d1dd19
-- title:
--   Height Descent Minors: to ZMod ne zero of mem mu alt
-- statement:
--   The Height Descent Minors construction uses the to ZMod ne zero of mem mu alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L625-L625
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L625-L625

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_ne_zero_of_mem_mu_alt {d : ℤ_[l]} (hd : d ∈ mu l) : PadicInt.toZMod d ≠ 0 := by sorry
