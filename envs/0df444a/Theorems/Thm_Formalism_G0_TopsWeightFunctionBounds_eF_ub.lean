-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_eF_ub
-- name    : Formalism.G0.TopsWeightFunctionBounds.eF_ub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:32.694137+00:00
-- url     : https://prove2.me/theorems/9b638db4-4581-4b9e-9628-d10df49fa55d
-- title:
--   Tops Weight Function Bounds: e F ub
-- statement:
--   The Tops Weight Function Bounds construction uses the e F ub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L92-L95

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

theorem Formalism.G0.TopsWeightFunctionBounds.eF_ub (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (d : ℕ) : eF δ d ≤ 1 / (2 - δ) := by sorry
