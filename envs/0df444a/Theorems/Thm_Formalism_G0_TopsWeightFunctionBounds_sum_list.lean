-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_sum_list
-- name    : Formalism.G0.TopsWeightFunctionBounds.sum_list
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:48.592917+00:00
-- url     : https://prove2.me/theorems/b8bcad32-82c2-4f1e-8467-bd9770eba903
-- title:
--   Tops Weight Function Bounds: sum list
-- statement:
--   The Tops Weight Function Bounds construction uses the sum list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L370-L415
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L370-L415

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

theorem Formalism.G0.TopsWeightFunctionBounds.sum_list (l : List ℕ) (hl : l.Nodup) : ∀ s : St,
    ∑ U ∈ l.toFinset.powerset,
      (if runS R L₂ s (l.map (fun p => decide (p ∈ U))) = .bad then
        ∏ p ∈ l.toFinset, wP δ U p else 0) = Wt R L₂ δ l.length s := by sorry
