-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_intTwoSided
-- name    : Formalism.DoubleCosetMeasures.P.intTwoSided
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T19:28:14.916192+00:00
-- url     : https://prove2.me/theorems/5df1792b-d831-4030-9597-aa7a2f8b3bb3
-- title:
--   P: int Two Sided
-- statement:
--   The P construction uses the int Two Sided property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/TwoSided.lean#L51-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/TwoSided.lean#L51-L129

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_TwoSided
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P

theorem Formalism.DoubleCosetMeasures.P.intTwoSided : Formalism.DoubleCosetMeasures.IntTwoSided := by sorry
