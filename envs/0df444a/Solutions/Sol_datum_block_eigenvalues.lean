-- Prove2me | solution 1 for datum_block_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:14:05.973636+00:00
-- url     : https://prove2.me/submissions/b4078188-f5c2-4d1e-89d5-ca1c3eb9ca20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumBlockEigen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_PhiUZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DatumBlockEigen
import Theorems.Thm_PI_DatumBlockEigen_Main_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.DatumBlockEigen := PI.DatumBlockEigen.Main.main
