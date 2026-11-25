-- Prove2me | solution 1 for squarefree_roots_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:20:35.928448+00:00
-- url     : https://prove2.me/submissions/7b1ecc43-f11e-4633-8e3c-8784f0632ea2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqfRootsInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_RpowQuarterPowFour
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SqfRootsInj
import Theorems.Thm_PI_SqfRootsInj_W_claim_of
import Theorems.Thm_PI_SqfRootsInj_W_counted_labels_have_witness
import Theorems.Thm_PI_SqfRootsInj_W_local_orbit_count


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.SqfRootsInj.Claim :=
  PI.SqfRootsInj.W.claim_of PI.SqfRootsInj.W.counted_labels_have_witness PI.SqfRootsInj.W.local_orbit_count
