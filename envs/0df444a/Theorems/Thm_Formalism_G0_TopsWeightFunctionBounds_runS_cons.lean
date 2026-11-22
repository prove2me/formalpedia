-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_runS_cons
-- name    : Formalism.G0.TopsWeightFunctionBounds.runS_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:52.102707+00:00
-- url     : https://prove2.me/theorems/626a1ea7-f6e0-4485-a173-86927a63cb15
-- title:
--   Tops Weight Function Bounds: run S cons
-- statement:
--   The Tops Weight Function Bounds construction uses the run S cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L355-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L355-L356

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {R L₂ : ℕ} {δ : ℝ}

theorem Formalism.G0.TopsWeightFunctionBounds.runS_cons (s : St) (b : Bool) (bs : List Bool) :
    runS R L₂ s (b :: bs) = runS R L₂ (step R L₂ s b) bs := by sorry
