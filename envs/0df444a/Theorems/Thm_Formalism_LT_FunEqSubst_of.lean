-- Prove2me | Theorems.Thm_Formalism_LT_FunEqSubst_of
-- name    : Formalism.LT.FunEqSubst_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:58.049738+00:00
-- url     : https://prove2.me/theorems/90663c40-0a75-4185-b680-8d3c8b633b2c
-- title:
--   LT: Fun Eq Subst of
-- statement:
--   The LT construction uses the Fun Eq Subst of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormSigmaLeOne.lean#L43-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormSigmaLeOne.lean#L43-L137

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
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
universe u v
open Formalism Formalism.LT
open Formalism.G
open InverseIntegralClassesKeyFacts

theorem Formalism.LT.FunEqSubst_of (h4 : Formalism.LT.IntegralSubst.{u, v}) (h5 : Formalism.LT.CoeffBound.{u})
    (h6 : Formalism.LT.PowCongr.{u, v}) (h7 : Formalism.LT.FrobCongr.{u, v}) : Formalism.G.FunEqSubst.{u, v} := by sorry
