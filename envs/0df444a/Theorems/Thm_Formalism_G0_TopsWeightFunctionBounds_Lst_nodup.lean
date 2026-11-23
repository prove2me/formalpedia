-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_Lst_nodup
-- name    : Formalism.G0.TopsWeightFunctionBounds.Lst_nodup
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:18.694695+00:00
-- url     : https://prove2.me/theorems/a99afbd0-df5e-4668-ad71-81bc7e5233b2
-- title:
--   Tops Weight Function Bounds: Lst nodup
-- statement:
--   The Tops Weight Function Bounds construction uses the Lst nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L435-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L435-L441

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

theorem Formalism.G0.TopsWeightFunctionBounds.Lst_nodup (n i : ℕ) : (Lst n i).Nodup := by sorry
