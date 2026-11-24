-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_two_le_inf
-- name    : Formalism.IndefR.Eqv.two_le_inf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:27.733275+00:00
-- url     : https://prove2.me/theorems/2cc84f78-430a-4b75-bdb8-2118ec126b47
-- title:
--   Eqv: two le inf
-- statement:
--   The Eqv construction uses the two le inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/SobSym.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/SobSym.lean#L14-L16

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

theorem Formalism.IndefR.Eqv.two_le_inf : minSmoothness ℝ 2 ≤ ∞ := by sorry
