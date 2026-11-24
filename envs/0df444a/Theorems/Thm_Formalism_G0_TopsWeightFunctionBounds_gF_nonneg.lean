-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_gF_nonneg
-- name    : Formalism.G0.TopsWeightFunctionBounds.gF_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:33.645072+00:00
-- url     : https://prove2.me/theorems/9df9140c-f20b-4eab-832a-4d5800464b7d
-- title:
--   Tops Weight Function Bounds: g F nonneg
-- statement:
--   The Tops Weight Function Bounds construction uses the g F nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L97-L102

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

theorem Formalism.G0.TopsWeightFunctionBounds.gF_nonneg (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j d : ℕ) (ev : Bool) : 0 ≤ gF L₂ δ j d ev := by sorry
