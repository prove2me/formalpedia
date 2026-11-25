-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_ge_intCast
-- name    : Formalism.L2.FormalSeriesBounds.FrobP.ge_intCast
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:36:01.466259+00:00
-- url     : https://prove2.me/theorems/4b88493d-5fac-4f08-821e-a656e0fef4bd
-- title:
--   Frob P: ge int Cast
-- statement:
--   The Frob P construction uses the ge int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffPowCharFrobenius.lean#L14-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffPowCharFrobenius.lean#L14-L28

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffPowCharFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open ValuationNonnegativity
open Formalism.L2.FormalSeriesBounds.FrobP
variable {C : Type} [Field C] {V : VF C}

theorem Formalism.L2.FormalSeriesBounds.FrobP.ge_intCast (z : ℤ) : V.Ge 0 (z : C) := by sorry
