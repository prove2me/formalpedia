-- Prove2me | solution 1 for exists_periodPairOfIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:34:50.166082+00:00
-- url     : https://prove2.me/submissions/9b7ae677-a369-4e34-97b9-c0535883f4b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PeriodPairIndependence_IndepOfImNe
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KerPerPair
import Theorems.Thm_PI_KerLat_PerPairProof_perPair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.KerLat.PerPair := PI.KerLat.PerPairProof.perPair
