-- Prove2me | solution 1 for covector_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:09:02.506202+00:00
-- url     : https://prove2.me/submissions/00803364-a5f8-48fb-be25-3024934d9cbe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianCovectors_HermBvecLeft
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CovecEntries
import Theorems.Thm_CovecW_covec_entries


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.C3.XiYZhat := CovecW.covec_entries
