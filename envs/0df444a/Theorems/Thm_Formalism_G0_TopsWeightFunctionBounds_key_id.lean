-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_key_id
-- name    : Formalism.G0.TopsWeightFunctionBounds.key_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:45.784907+00:00
-- url     : https://prove2.me/theorems/44dfcf60-cb80-4897-af0c-f4da2d0c01c3
-- title:
--   Tops Weight Function Bounds: key id
-- statement:
--   The Tops Weight Function Bounds construction uses the key id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L70-L73

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
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {L₂ : ℕ} {δ : ℝ}

theorem Formalism.G0.TopsWeightFunctionBounds.key_id (h1 : δ ≤ 1) : δ * 1 + (1 - δ) * ((1 - δ) / (2 - δ)) = 1 / (2 - δ) := by sorry
