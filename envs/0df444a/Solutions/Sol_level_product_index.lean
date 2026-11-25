-- Prove2me | solution 1 for level_product_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:07:44.740331+00:00
-- url     : https://prove2.me/submissions/51eae11a-28b2-438b-bbdd-614d67dfeed1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LevelProdIdx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_ZeroMemLatSet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVTmulEqTmulApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVMemTensInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_SingleApply
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LevelProdIdx
import Theorems.Thm_PI_LPI_levelProdIdx_of
import Theorems.Thm_PI_LPI_plDown
import Theorems.Thm_PI_LPI_plGen
import Theorems.Thm_PI_LPI_plInj
import Theorems.Thm_PI_LPI_plLocal_of
import Theorems.Thm_PI_LPI_plUp_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.LevelProdIdx :=
  PI.LPI.levelProdIdx_of PI.LPI.plDown (PI.LPI.plUp_of PI.LPI.plGen PI.LPI.plInj)
    (PI.LPI.plLocal_of PI.LPI.plGen PI.LPI.plDown)
