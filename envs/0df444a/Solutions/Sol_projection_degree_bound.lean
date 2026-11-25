-- Prove2me | solution 1 for projection_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:07:44.748641+00:00
-- url     : https://prove2.me/submissions/9769cecd-63b7-4a5f-b005-b3dd813b0dac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MajorantVanishing_MajAtZeroRight
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DvProjB
import Theorems.Thm_PI_Dv_ProjBW_projB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.Dv.ProjB := PI.Dv.ProjBW.projB
