-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_br_padic
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.hasSubst_br_padic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:00.424134+00:00
-- url     : https://prove2.me/theorems/349b5be3-0498-4af4-bd33-c261ea418da9
-- title:
--   Height Descent Minors: has Subst br padic
-- statement:
--   The Height Descent Minors construction uses the has Subst br padic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L137-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L137-L140

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.hasSubst_br_padic (c : ℤ_[l]) : HasSubst (br l O c) := by sorry
