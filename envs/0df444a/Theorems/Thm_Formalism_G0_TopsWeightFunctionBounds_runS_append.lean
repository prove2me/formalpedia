-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_runS_append
-- name    : Formalism.G0.TopsWeightFunctionBounds.runS_append
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:52.23283+00:00
-- url     : https://prove2.me/theorems/7f360d7d-4f71-4736-bb4a-8f495209a64f
-- title:
--   Tops Weight Function Bounds: run S append
-- statement:
--   The Tops Weight Function Bounds construction uses the run S append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L358-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L358-L360

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

theorem Formalism.G0.TopsWeightFunctionBounds.runS_append (s : St) (l₁ l₂ : List Bool) :
    runS R L₂ s (l₁ ++ l₂) = runS R L₂ (runS R L₂ s l₁) l₂ := by sorry
