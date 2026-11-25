-- Prove2me | solution 1 for inf_eq_inter_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:30:59.916482+00:00
-- url     : https://prove2.me/submissions/9adf3667-3f21-46dc-ae24-3b414035e768

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_LocLatSat
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LocLatSat
import Theorems.Thm_PI_LocLatSat_UnitaryGroupMassFormula_locLatSat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.LocLatSat.Stmt := PI.LocLatSat.UnitaryGroupMassFormula.locLatSat
