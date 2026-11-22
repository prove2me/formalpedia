-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_mem_units_of_mem_mu
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_mem_units_of_mem_mu
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:54.932022+00:00
-- url     : https://prove2.me/theorems/b6ca99b4-38d6-47c2-a200-4d05576bac29
-- title:
--   Height Descent Minors: to ZMod mem units of mem mu
-- statement:
--   The Height Descent Minors construction uses the to ZMod mem units of mem mu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L266-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L266-L266

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_mem_units_of_mem_mu : ∀ d ∈ mu l, PadicInt.toZMod d ∈ (univ.erase (0 : ZMod l)) := by sorry
