-- Prove2me | solution 1 for quantum_minor_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:17:35.758825+00:00
-- url     : https://prove2.me/submissions/e9fe6d15-037b-44c8-910a-37f60ddd3de6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RTTIndependence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumMinorLemma_Imports
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmLemD
import Theorems.Thm_PI_QmLemDWork_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.LemmaD := PI.QmLemDWork.main
