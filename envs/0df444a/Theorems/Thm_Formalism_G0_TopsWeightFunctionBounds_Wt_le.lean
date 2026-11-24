-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_Wt_le
-- name    : Formalism.G0.TopsWeightFunctionBounds.Wt_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:24.454942+00:00
-- url     : https://prove2.me/theorems/231f6725-3500-43db-97ef-8debefb96df3
-- title:
--   Tops Weight Function Bounds: Wt le
-- statement:
--   The Tops Weight Function Bounds construction uses the Wt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L321-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L321-L339

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

theorem Formalism.G0.TopsWeightFunctionBounds.Wt_le (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (hR : 1 ≤ R) (m : ℕ) :
    ∀ s, WF R s → Wt R L₂ δ m s ≤ Phi R L₂ δ s := by sorry
