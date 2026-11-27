-- Prove2me | solution 1 for kernel_four_squares
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:35:22.025689+00:00
-- url     : https://prove2.me/submissions/3c0a9099-17bb-488f-ac2b-ab9f1f03b680

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOfFromDiag
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KerFourSq
import Theorems.Thm_PI_KerIso_FourSqW_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.KerIso.FourSq :=
  PI.KerIso.FourSqW.main
