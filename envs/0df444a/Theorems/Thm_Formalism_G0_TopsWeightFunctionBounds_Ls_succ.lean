-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_Ls_succ
-- name    : Formalism.G0.TopsWeightFunctionBounds.Ls_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:47.388956+00:00
-- url     : https://prove2.me/theorems/39de490b-516b-4067-a5a4-e404eb602018
-- title:
--   Tops Weight Function Bounds: Ls succ
-- statement:
--   The Tops Weight Function Bounds construction uses the Ls succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L704-L712
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L704-L712

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

theorem Formalism.G0.TopsWeightFunctionBounds.Ls_succ (n : ℕ) (T : Finset ℕ) (b t m : ℕ) :
    Ls n T b t (m + 1) = decide ((b + (t + 1)) % n ∈ T) :: Ls n T b (t + 1) m := by sorry
