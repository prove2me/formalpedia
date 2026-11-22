-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_mem_cls
-- name    : Formalism.DoubleCosetMeasures.P.mem_cls
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:43:22.508588+00:00
-- url     : https://prove2.me/theorems/fbe344a9-a122-46d9-82da-d504a1c41b58
-- title:
--   P: mem cls
-- statement:
--   The P construction uses the mem cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L15-L16

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

theorem Formalism.DoubleCosetMeasures.P.mem_cls {r : Setoid X} {q : Quotient r} {y : X} :
    y ∈ cls r q ↔ Quotient.mk r y = q := by sorry
