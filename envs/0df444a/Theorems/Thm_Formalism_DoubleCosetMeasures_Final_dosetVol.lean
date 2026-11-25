-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_Final_dosetVol
-- name    : Formalism.DoubleCosetMeasures.Final.dosetVol
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:24:23.090595+00:00
-- url     : https://prove2.me/theorems/20167fdd-77d7-44fd-baa3-69d142f20921
-- title:
--   Final: doset Vol
-- statement:
--   The Final construction uses the doset Vol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LatticeCoset.lean#L22-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LatticeCoset.lean#L22-L22

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_TwoSided
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementZ
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_dosetVol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.Final
open Formalism.DoubleCosetMeasures

theorem Formalism.DoubleCosetMeasures.Final.dosetVol : Formalism.DoubleCosetMeasures.DosetVol := by sorry
