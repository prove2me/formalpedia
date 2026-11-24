-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_natCast_lt_inf
-- name    : Formalism.IndefR.Eqv.natCast_lt_inf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:23:20.233774+00:00
-- url     : https://prove2.me/theorems/7fe0dbd1-dddb-4fed-bbe1-f7836e957ff1
-- title:
--   Eqv: nat Cast lt inf
-- statement:
--   The Eqv construction uses the nat Cast lt inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/IterEqOfRange.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/IterEqOfRange.lean#L24-L25

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
import Definitions.Def_Formalism_FlagUnipotentLattices_KappaAssemblyOf
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterEqOfRange
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
open MeasureTheory
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.IndefR.Eqv.natCast_lt_inf (m : ℕ) : (m : WithTop ℕ∞) < ∞ := by sorry
