-- Prove2me | solution 1 for geometric_product_power
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:08:06.208835+00:00
-- url     : https://prove2.me/submissions/77771c70-75ef-4a21-a4c4-bcf0d5b49db5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GeometricProductPowers_GaussianProductPowerBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeometricProductBound_OneSubSumLeProd
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_GeoProdPow
import Theorems.Thm_GeoProdPow_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : ConditionalKappaBounds.G2.GaussianProductPowerBound := GeoProdPow.main
