-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_WF_step
-- name    : Formalism.G0.TopsWeightFunctionBounds.WF_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:57.787979+00:00
-- url     : https://prove2.me/theorems/4f25e320-ad9e-49e0-bf6c-f5d900f717fb
-- title:
--   Tops Weight Function Bounds: WF step
-- statement:
--   The Tops Weight Function Bounds construction uses the WF step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L230-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L230-L243

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
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {R L₂ : ℕ} {δ : ℝ}

theorem Formalism.G0.TopsWeightFunctionBounds.WF_step (hR : 1 ≤ R) (s : St) (hs : WF R s) (b : Bool) : WF R (step R L₂ s b) := by sorry
