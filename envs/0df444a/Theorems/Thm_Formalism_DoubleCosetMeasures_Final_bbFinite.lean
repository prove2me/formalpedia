-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_Final_bbFinite
-- name    : Formalism.DoubleCosetMeasures.Final.bbFinite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:51.109586+00:00
-- url     : https://prove2.me/theorems/62ee5f73-8a8a-4061-8e28-406b33d12c7a
-- title:
--   Final: bb Finite
-- statement:
--   The Final construction uses the bb Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LatticeCoset.lean#L30-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LatticeCoset.lean#L30-L30

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

theorem Formalism.DoubleCosetMeasures.Final.bbFinite : Formalism.DoubleCosetMeasures.BBFinite := by sorry
