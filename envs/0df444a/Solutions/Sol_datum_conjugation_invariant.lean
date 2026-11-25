-- Prove2me | solution 1 for datum_conjugation_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:28:11.076497+00:00
-- url     : https://prove2.me/submissions/36b3384e-4ec9-493d-9059-34d90f67cfba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumConjInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugationInvariance_SecondRowsBlockDiagMul
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DatumConjInv
import Theorems.Thm_PI_DatumConjInvWork_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.DatumConjInv := PI.DatumConjInvWork.main
