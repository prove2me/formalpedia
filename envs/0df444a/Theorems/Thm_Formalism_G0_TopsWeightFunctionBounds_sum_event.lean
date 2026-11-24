-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_sum_event
-- name    : Formalism.G0.TopsWeightFunctionBounds.sum_event
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:31.341718+00:00
-- url     : https://prove2.me/theorems/0d15031d-21ea-4905-9f75-73f91fca444c
-- title:
--   Tops Weight Function Bounds: sum event
-- statement:
--   The Tops Weight Function Bounds construction uses the sum event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L474-L516
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L474-L516

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

theorem Formalism.G0.TopsWeightFunctionBounds.sum_event {n i : ℕ} (hi : i < n) (s : St) :
    ∑ T ∈ (Finset.range n).powerset,
      (if i ∈ T ∧ runS R L₂ s ((Lst n i).map (fun p => decide (p ∈ T))) = .bad then
        ∏ p ∈ Finset.range n, wP δ T p else 0) = δ * Wt R L₂ δ (n - 1) s := by sorry
