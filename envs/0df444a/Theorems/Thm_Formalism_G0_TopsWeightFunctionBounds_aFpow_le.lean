-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_aFpow_le
-- name    : Formalism.G0.TopsWeightFunctionBounds.aFpow_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:32.693427+00:00
-- url     : https://prove2.me/theorems/bd86cc9e-92ab-4499-98d9-7982a1889bc7
-- title:
--   Tops Weight Function Bounds: a Fpow le
-- statement:
--   The Tops Weight Function Bounds construction uses the a Fpow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L208-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L208-L209

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
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {R L₂ : ℕ} {δ : ℝ}

theorem Formalism.G0.TopsWeightFunctionBounds.aFpow_le (h0 : 0 ≤ δ) (hLδ : (L₂ : ℝ) * δ ≤ 1) (k : ℕ) : aF L₂ δ ^ k ≤ 1 := by sorry
