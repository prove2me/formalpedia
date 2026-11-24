-- Prove2me | Theorems.Thm_Formalism_LT_Asm_map_subst2
-- name    : Formalism.LT.Asm.map_subst2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:50:37.476005+00:00
-- url     : https://prove2.me/theorems/e9f3ca71-40c5-474b-81f5-0f85fed401c6
-- title:
--   Asm: map subst2
-- statement:
--   The Asm construction uses the map subst2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L159-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L159-L170

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

theorem Formalism.LT.Asm.map_subst2 {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {τ : Type*}
    (Φ : MvPowerSeries (Fin 2) A) {u v : MvPowerSeries τ A}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    MvPowerSeries.map φ (Φ.subst ![u, v]) =
      (MvPowerSeries.map φ Φ).subst ![MvPowerSeries.map φ u, MvPowerSeries.map φ v] := by sorry
