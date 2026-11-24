-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_inf_add_nat
-- name    : Formalism.IndefR.Eqv.inf_add_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:35.506179+00:00
-- url     : https://prove2.me/theorems/c97a6080-1ae2-4e71-b6fe-caf20333c45a
-- title:
--   Eqv: inf add nat
-- statement:
--   The Eqv construction uses the inf add nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/SobSym.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/SobSym.lean#L18-L22

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

theorem Formalism.IndefR.Eqv.inf_add_nat (m : ℕ) : (∞ : WithTop ℕ∞) + (m : WithTop ℕ∞) ≤ ∞ := by sorry
