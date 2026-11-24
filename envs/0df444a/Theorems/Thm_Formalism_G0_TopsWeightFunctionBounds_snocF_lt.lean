-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_snocF_lt
-- name    : Formalism.G0.TopsWeightFunctionBounds.snocF_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:52.991163+00:00
-- url     : https://prove2.me/theorems/673cd0da-7479-4d94-af83-9d4ec1e62eee
-- title:
--   Tops Weight Function Bounds: snoc F lt
-- statement:
--   The Tops Weight Function Bounds construction uses the snoc F lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L553-L554
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L553-L554

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

theorem Formalism.G0.TopsWeightFunctionBounds.snocF_lt {j : ℕ} (u : Fin j → ℕ) (v : ℕ) (l : Fin (j + 1)) (h : l.val < j) :
    snocF u v l = u ⟨l.val, h⟩ := by sorry
