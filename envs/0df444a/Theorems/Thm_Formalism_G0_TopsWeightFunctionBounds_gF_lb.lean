-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_gF_lb
-- name    : Formalism.G0.TopsWeightFunctionBounds.gF_lb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:38.481557+00:00
-- url     : https://prove2.me/theorems/63cb1350-89d3-47be-8ccc-96452477e1df
-- title:
--   Tops Weight Function Bounds: g F lb
-- statement:
--   The Tops Weight Function Bounds construction uses the g F lb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L116-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L116-L149

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

theorem Formalism.G0.TopsWeightFunctionBounds.gF_lb (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (j : ℕ) (ev : Bool) :
    aF L₂ δ ≤ gF L₂ δ j 0 ev := by sorry
