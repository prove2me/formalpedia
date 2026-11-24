-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_runS_bad
-- name    : Formalism.G0.TopsWeightFunctionBounds.runS_bad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:55.373903+00:00
-- url     : https://prove2.me/theorems/79cfc3d2-d929-4c14-b38f-10ac1916fabc
-- title:
--   Tops Weight Function Bounds: run S bad
-- statement:
--   The Tops Weight Function Bounds construction uses the run S bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L362-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L362-L368

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

theorem Formalism.G0.TopsWeightFunctionBounds.runS_bad (bs : List Bool) : runS R L₂ .bad bs = .bad := by sorry
