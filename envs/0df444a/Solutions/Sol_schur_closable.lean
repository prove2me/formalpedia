-- Prove2me | solution 1 for schur_closable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:13:12.889201+00:00
-- url     : https://prove2.me/submissions/cf50b1ce-cbec-4ca6-a541-40987b5b7734

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_SchurClosable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurUnitaryInner_UnitaryInner
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SchurClosable
import Theorems.Thm_PI_UnitaryGroupMassFormula_SchurClosable_Main_schurClosable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.IndefR.Leaf.SchurClosable :=
  PI.UnitaryGroupMassFormula.SchurClosable.Main.schurClosable
