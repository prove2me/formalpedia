-- Prove2me | solution 1 for dvProjC_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:07:40.145365+00:00
-- url     : https://prove2.me/submissions/f35cdc5e-5405-4e45-8c4f-d23c3f784bca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSpans_SpanPowSmul
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DvIdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DvProjC
import Theorems.Thm_PI_Dv_ProjCW_projC_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution (h : PI.Dv.IdxCalc) : PI.Dv.ProjC := PI.Dv.ProjCW.projC_of h
