-- Prove2me | Theorems.Thm_Formalism_LT_Asm_log_subst2
-- name    : Formalism.LT.Asm.log_subst2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:50:08.772517+00:00
-- url     : https://prove2.me/theorems/a998bd2d-6da7-4f07-b8f8-5d0aab19b0d1
-- title:
--   Asm: log subst2
-- statement:
--   The Asm construction uses the log subst2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L123-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L123-L132

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
open Formalism Formalism.LT Formalism.LT.Asm
open Formalism.G
open Formalism.G.LogP

theorem Formalism.LT.Asm.log_subst2 {R : Type*} [CommRing R] {τ : Type*} (f : PowerSeries R)
    (F : MvPowerSeries (Fin 2) R) (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF : f.subst F = atX f + atY f) {u v : MvPowerSeries τ R}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    f.subst (F.subst ![u, v]) = f.subst u + f.subst v := by sorry
