-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_iterSymmR
-- name    : Formalism.IndefR.Eqv.iterSymmR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:15.178433+00:00
-- url     : https://prove2.me/theorems/b5b7ce2a-1eed-4331-9816-59cc0be8428b
-- title:
--   Eqv: iter Symm R
-- statement:
--   The Eqv construction uses the iter Symm R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/SobSym.lean#L106-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/SobSym.lean#L106-L119

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.IndefR.Eqv.iterSymmR : IterSymmR := by sorry
