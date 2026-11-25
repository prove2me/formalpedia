-- Prove2me | solution 1 for self_dual_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:02:57.031805+00:00
-- url     : https://prove2.me/submissions/ed0a3af3-693d-445e-b52b-3230044d6708

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_SelfDualLocOfLocBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_LocBasis
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SelfDualLoc
import Theorems.Thm_PI_SelfDualLoc_W_locBasis
import Theorems.Thm_PI_SelfDualLoc_W_selfDualLoc_of_locBasis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.SelfDualLoc :=
  PI.SelfDualLoc.W.selfDualLoc_of_locBasis PI.SelfDualLoc.W.locBasis
