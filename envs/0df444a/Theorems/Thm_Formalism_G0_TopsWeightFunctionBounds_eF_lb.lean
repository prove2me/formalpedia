-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_eF_lb
-- name    : Formalism.G0.TopsWeightFunctionBounds.eF_lb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:43.369808+00:00
-- url     : https://prove2.me/theorems/fefc5988-761c-419e-a2a1-2492a6fc275d
-- title:
--   Tops Weight Function Bounds: e F lb
-- statement:
--   The Tops Weight Function Bounds construction uses the e F lb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L87-L90

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

theorem Formalism.G0.TopsWeightFunctionBounds.eF_lb (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (d : ℕ) : (1 - δ) / (2 - δ) ≤ eF δ d := by sorry
