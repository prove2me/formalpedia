-- Prove2me | solution 1 for gradedOscillatorProperty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:06.096339+00:00
-- url     : https://prove2.me/submissions/23a99b7b-b1a0-4a9b-a45d-e2b781af4e3b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_GradedOscillatorPropertyOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_KroneckerMapOneRightNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockRaiseLow
import Theorems.Thm_FockRL_adjStep_of
import Theorems.Thm_FockRL_blockDiagonalPreservesDegree
import Theorems.Thm_FockRL_gradedOscillatorProperty_of
import Theorems.Thm_FockRL_kroneckerProperties
import Theorems.Thm_FockRL_pcStep_of
import Theorems.Thm_FockRaiseLowGrade_raisingLoweringSplit
import Theorems.Thm_FockRaiseLowInner_fischerConjLinearLeft
import Theorems.Thm_FockRaiseLowInner_fischerLinearRight
import Theorems.Thm_FockRaiseLowInner_fischerXAdjoint


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : FockH1Action.H1 :=
  FockRL.gradedOscillatorProperty_of FockRL.blockDiagonalPreservesDegree
    (FockRL.pcStep_of FockRaiseLowGrade.raisingLoweringSplit)
    (FockRL.adjStep_of FockRaiseLowGrade.raisingLoweringSplit FockRaiseLowInner.fischerConjLinearLeft
      FockRaiseLowInner.fischerLinearRight FockRaiseLowInner.fischerXAdjoint)
    FockRL.kroneckerProperties
