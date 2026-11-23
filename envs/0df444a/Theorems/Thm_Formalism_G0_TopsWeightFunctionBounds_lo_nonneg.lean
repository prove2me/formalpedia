-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_lo_nonneg
-- name    : Formalism.G0.TopsWeightFunctionBounds.lo_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:46.639923+00:00
-- url     : https://prove2.me/theorems/8f407b86-aa28-4f91-9317-d9db405bf92e
-- title:
--   Tops Weight Function Bounds: lo nonneg
-- statement:
--   The Tops Weight Function Bounds construction uses the lo nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L83-L85

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

theorem Formalism.G0.TopsWeightFunctionBounds.lo_nonneg (h1 : δ ≤ 1) : 0 ≤ (1 - δ) / (2 - δ) := by sorry
