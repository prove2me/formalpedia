-- Prove2me | solution 1 for transference_covering
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:38.942135+00:00
-- url     : https://prove2.me/submissions/bc31ab02-bb38-4811-ae45-f58376768136

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Skeleton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Poisson
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_NumericMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_KeySmall
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceCover
import Theorems.Thm_P2M_PI_Tr_transferenceCover_of__d6bd68747b26
import Theorems.Thm_PI_Tr_gaussStep
import Theorems.Thm_PI_Tr_keySmall
import Theorems.Thm_PI_Tr_poissonGauss


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall
