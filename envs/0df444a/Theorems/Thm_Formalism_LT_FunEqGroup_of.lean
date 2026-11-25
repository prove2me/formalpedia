-- Prove2me | Theorems.Thm_Formalism_LT_FunEqGroup_of
-- name    : Formalism.LT.FunEqGroup_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:56.317101+00:00
-- url     : https://prove2.me/theorems/bae1bf76-e081-4131-a4ce-bf2791cebd0e
-- title:
--   LT: Fun Eq Group of
-- statement:
--   The LT construction uses the Fun Eq Group of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L262-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L262-L264

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT

theorem Formalism.LT.FunEqGroup_of (h1 : Formalism.LT.SolveExists.{u, 0}) (h2 : Formalism.LT.InvIntegralOfClass.{u, 0})
    (h3 : Formalism.LT.FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqGroup.{u} := by sorry
