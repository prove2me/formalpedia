-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_surjOn_mu_nonzero
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_surjOn_mu_nonzero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:04.74644+00:00
-- url     : https://prove2.me/theorems/2f791a68-14fd-452a-af7d-2bc0c910dfcb
-- title:
--   Height Descent Minors: to ZMod surj On mu nonzero
-- statement:
--   The Height Descent Minors construction uses the to ZMod surj On mu nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L272-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L272-L277

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_surjOn_mu_nonzero : Set.SurjOn (PadicInt.toZMod (p := l)) (mu l : Set ℤ_[l])
    ((univ.erase (0 : ZMod l) : Finset (ZMod l)) : Set (ZMod l)) := by sorry
