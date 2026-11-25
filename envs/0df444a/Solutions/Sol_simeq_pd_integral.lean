-- Prove2me | solution 1 for simeq_pd_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:13:24.375849+00:00
-- url     : https://prove2.me/submissions/0aebd480-c148-4944-9356-427af873ca52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SimeqPdInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialCoefficientSeries_CoeffExpMvEqTs
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SimeqPdInt
import Theorems.Thm_PI_UnitaryGroupMassFormula_SimeqPdInt_target


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.SimeqPdInt.Target := PI.UnitaryGroupMassFormula.SimeqPdInt.target
