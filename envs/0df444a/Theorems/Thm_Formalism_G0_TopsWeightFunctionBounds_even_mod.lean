-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_even_mod
-- name    : Formalism.G0.TopsWeightFunctionBounds.even_mod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:44.465722+00:00
-- url     : https://prove2.me/theorems/eaa2f643-ce35-4ea1-a045-bb72185ea0ab
-- title:
--   Tops Weight Function Bounds: even mod
-- statement:
--   The Tops Weight Function Bounds construction uses the even mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L559-L560
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L559-L560

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

theorem Formalism.G0.TopsWeightFunctionBounds.even_mod {n : ℕ} (hn : Even n) (x : ℕ) : Even (x % n) ↔ Even x := by sorry
