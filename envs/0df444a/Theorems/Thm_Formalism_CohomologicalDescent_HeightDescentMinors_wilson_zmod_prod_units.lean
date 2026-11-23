-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_wilson_zmod_prod_units
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.wilson_zmod_prod_units
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:41.376295+00:00
-- url     : https://prove2.me/theorems/b8e42914-9641-4c38-8043-4bbee0afd893
-- title:
--   Height Descent Minors: wilson zmod prod units
-- statement:
--   The Height Descent Minors construction uses the wilson zmod prod units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L283-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L283-L306

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.wilson_zmod_prod_units : ∏ x ∈ (univ.erase (0 : ZMod l)), x = -1 := by sorry
