-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_bbFinite_of
-- name    : Formalism.DoubleCosetMeasures.P.bbFinite_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:28.484869+00:00
-- url     : https://prove2.me/theorems/34f10109-f67c-423f-8c72-0754f967c54d
-- title:
--   P: bb Finite of
-- statement:
--   The P construction uses the bb Finite of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsOpenIsIntSet.lean#L94-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsOpenIsIntSet.lean#L94-L101

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

theorem Formalism.DoubleCosetMeasures.P.bbFinite_of : IntTwoSided → IntInv → IsoInv → SimpleAdd → BBFinite := by sorry
