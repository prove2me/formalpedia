-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_support_out_finite
-- name    : Formalism.DoubleCosetMeasures.P.support_out_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:14.227004+00:00
-- url     : https://prove2.me/theorems/493539c0-3be7-4304-98ef-912e7096f62d
-- title:
--   P: support out finite
-- statement:
--   The P construction uses the support out finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L21-L30

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
variable {X : Type}
variable [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem Formalism.DoubleCosetMeasures.P.support_out_finite (r : Setoid X) (hr : ∀ q, IsOpen (cls r q)) (f : X → E)
    (hc : HasCompactSupport f) :
    (Function.support (fun q : Quotient r => f q.out)).Finite := by sorry
