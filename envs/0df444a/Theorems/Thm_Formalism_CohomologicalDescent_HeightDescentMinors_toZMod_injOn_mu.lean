-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_injOn_mu
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_injOn_mu
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:40.084509+00:00
-- url     : https://prove2.me/theorems/7762b29c-6cc4-4243-bf97-fcf260cbf6d5
-- title:
--   Height Descent Minors: to ZMod inj On mu
-- statement:
--   The Height Descent Minors construction uses the to ZMod inj On mu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L268-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L268-L270

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_injOn_mu : Set.InjOn (PadicInt.toZMod (p := l)) (mu l : Set ℤ_[l]) := by sorry
