-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_restriction
-- name    : Formalism.CyclotomicNorms.restriction
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:36:52.295269+00:00
-- url     : https://prove2.me/theorems/5ec19411-f4f4-421f-b294-8a64401a469b
-- title:
--   Cyclotomic Norms: restriction
-- statement:
--   The Cyclotomic Norms construction uses the restriction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/IrreducibilityOfGoodTuple.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/IrreducibilityOfGoodTuple.lean#L17-L17

import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Newton
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SpanQuadraticOfImage
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Cycles
import Definitions.Def_Formalism_TameInertiaTowers_FinalGroup
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Jordan
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_RestrictionOfBlocksAndJordan
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Definitions.Def_Formalism_CyclotomicNorms_IrreducibilityOfGoodTuple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CyclotomicNorms

theorem Formalism.CyclotomicNorms.restriction : Restriction := by sorry
