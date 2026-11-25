-- Prove2me | solution 1 for latLocGlob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:12:27.720485+00:00
-- url     : https://prove2.me/submissions/bbabea8d-2e0a-4ae2-8364-9eca1be76938

import Definitions.Def_Formalism_PeriodIntegrals_LatLocGlob
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalLattice_ExistsSmulMemOfLocal
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LatLocGlob
import Theorems.Thm_PI_LatLocGlob_Proof_latLocGlob_core


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.LatLocGlob.LatLocGlob := PI.LatLocGlob.Proof.latLocGlob_core
