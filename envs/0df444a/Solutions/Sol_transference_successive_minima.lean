-- Prove2me | solution 1 for transference_successive_minima
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:57:57.066043+00:00
-- url     : https://prove2.me/submissions/9950b72b-cad5-4cba-99b2-0a413141049b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Skeleton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Poisson
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_NumericMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_KeySmall
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Theorems.Thm_P2M_PI_Tr_transferenceMinima_of__e4ff42dc2360
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

theorem _root_.solution : PI.TransferenceMinima :=
  PI.Tr.transferenceMinima_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall
