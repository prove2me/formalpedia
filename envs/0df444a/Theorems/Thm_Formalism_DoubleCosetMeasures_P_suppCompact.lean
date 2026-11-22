-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_suppCompact
-- name    : Formalism.DoubleCosetMeasures.P.suppCompact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:57.594333+00:00
-- url     : https://prove2.me/theorems/adafb8d2-0bca-4bc9-a079-34a88585c378
-- title:
--   P: supp Compact
-- statement:
--   The P construction uses the supp Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L254-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L254-L325

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Supp

theorem Formalism.DoubleCosetMeasures.P.suppCompact : Formalism.DoubleCosetMeasures.SuppCompact := by sorry
