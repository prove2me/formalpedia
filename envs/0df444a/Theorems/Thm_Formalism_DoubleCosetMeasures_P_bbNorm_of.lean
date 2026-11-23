-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_bbNorm_of
-- name    : Formalism.DoubleCosetMeasures.P.bbNorm_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:35.858535+00:00
-- url     : https://prove2.me/theorems/dd1570d6-9282-44f3-b938-091b8bd6361b
-- title:
--   P: bb Norm of
-- statement:
--   The P construction uses the bb Norm of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsOpenIsIntSet.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsOpenIsIntSet.lean#L103-L106

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures

theorem Formalism.DoubleCosetMeasures.P.bbNorm_of : BBFinite → BBNorm := by sorry
