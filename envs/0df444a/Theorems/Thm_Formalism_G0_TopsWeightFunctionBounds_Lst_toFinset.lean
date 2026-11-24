-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_Lst_toFinset
-- name    : Formalism.G0.TopsWeightFunctionBounds.Lst_toFinset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:15.22552+00:00
-- url     : https://prove2.me/theorems/b8be8763-b0cb-48c8-bd7c-cd452bde02d8
-- title:
--   Tops Weight Function Bounds: Lst to Finset
-- statement:
--   The Tops Weight Function Bounds construction uses the Lst to Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L443-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L443-L472

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

theorem Formalism.G0.TopsWeightFunctionBounds.Lst_toFinset {n i : ℕ} (hi : i < n) : (Lst n i).toFinset = (Finset.range n).erase i := by sorry
