-- Prove2me | solution 1 for flag_gram_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:05:57.506177+00:00
-- url     : https://prove2.me/submissions/c39101a7-3ead-4ef9-a97f-2fc15080bd5e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramIsometryCoefficient_ExCoeffOneNe
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_GramIso
import Theorems.Thm_PI_UnitaryGroupMassFormula_GramIso_gramIso


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.FglGram.GramIso := PI.UnitaryGroupMassFormula.GramIso.gramIso
