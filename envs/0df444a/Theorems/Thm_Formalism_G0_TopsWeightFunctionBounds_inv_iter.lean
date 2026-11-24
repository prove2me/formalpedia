-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_inv_iter
-- name    : Formalism.G0.TopsWeightFunctionBounds.inv_iter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:35.093115+00:00
-- url     : https://prove2.me/theorems/61bbe3f4-c824-4af6-bfa8-d0d35b5535cb
-- title:
--   Tops Weight Function Bounds: inv iter
-- statement:
--   The Tops Weight Function Bounds construction uses the inv iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L714-L722
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L714-L722

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
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds

theorem Formalism.G0.TopsWeightFunctionBounds.inv_iter {n : ℕ} (hn : Even n) {T : Finset ℕ} {L₂ R b K₀ : ℕ} (hR : 1 ≤ R) (m : ℕ) :
    ∀ t s, Inv n T L₂ R b K₀ t s → Inv n T L₂ R b K₀ (t + m) (runS R L₂ s (Ls n T b t m)) := by sorry
