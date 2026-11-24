-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_gF_step
-- name    : Formalism.G0.TopsWeightFunctionBounds.gF_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:27.288258+00:00
-- url     : https://prove2.me/theorems/43674d0d-d8c4-4be0-b1a5-32bb8b15d2bb
-- title:
--   Tops Weight Function Bounds: g F step
-- statement:
--   The Tops Weight Function Bounds construction uses the g F step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L151-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L151-L194

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

theorem Formalism.G0.TopsWeightFunctionBounds.gF_step (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j d : ℕ) (ev : Bool) :
    gF L₂ δ j d ev ≤ δ * (if okG L₂ j d ev = true then 1 else 0) + (1 - δ) * gF L₂ δ j (d + 1) (!ev) := by sorry
