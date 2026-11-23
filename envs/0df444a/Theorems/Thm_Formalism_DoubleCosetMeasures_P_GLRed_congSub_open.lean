-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_congSub_open
-- name    : Formalism.DoubleCosetMeasures.P.GLRed.congSub_open
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:32.890299+00:00
-- url     : https://prove2.me/theorems/dc714c63-f107-40ad-b4d8-21595f259f9f
-- title:
--   GLRed: cong Sub open
-- statement:
--   The GLRed construction uses the cong Sub open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/RelIndexMulMeasure.lean#L199-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/RelIndexMulMeasure.lean#L199-L216

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Set Pointwise
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.GLRed
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

theorem Formalism.DoubleCosetMeasures.P.GLRed.congSub_open (O : Subring F) (hO : IsOpen (O : Set F)) (ϖ : F) (a : ℕ) :
    IsOpen (congSub O ϖ a : Set (GL (Fin a) F)) := by sorry
