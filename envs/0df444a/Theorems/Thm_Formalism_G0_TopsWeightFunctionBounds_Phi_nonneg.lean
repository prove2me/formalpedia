-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_Phi_nonneg
-- name    : Formalism.G0.TopsWeightFunctionBounds.Phi_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:25.614324+00:00
-- url     : https://prove2.me/theorems/725bf6b2-6289-441e-8a71-7f9ee6da8665
-- title:
--   Tops Weight Function Bounds: Phi nonneg
-- statement:
--   The Tops Weight Function Bounds construction uses the Phi nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L221-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L221-L228

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

theorem Formalism.G0.TopsWeightFunctionBounds.Phi_nonneg (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (s : St) :
    0 ≤ Phi R L₂ δ s := by sorry
