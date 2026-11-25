-- Prove2me | solution 1 for weyl_product_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:17:20.297994+00:00
-- url     : https://prove2.me/submissions/40f0fdd9-fc6b-4eae-a322-0cd98b603fba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylProduct_WeylProd
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WeylProd
import Theorems.Thm_PI_WeylProdWork_weylProd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.WeylProd := PI.WeylProdWork.weylProd
