-- Prove2me | Theorems.Thm_Formalism_LT_Asm_subst_zero_eq_rescale
-- name    : Formalism.LT.Asm.subst_zero_eq_rescale
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:18.991994+00:00
-- url     : https://prove2.me/theorems/21df201c-49f7-4573-a149-5f5ec3dc64ac
-- title:
--   Asm: subst zero eq rescale
-- statement:
--   The Asm construction uses the subst zero eq rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L141-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L141-L147

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

theorem Formalism.LT.Asm.subst_zero_eq_rescale {R : Type*} [CommRing R] (Φ : MvPowerSeries (Fin 2) R) :
    Φ.subst ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)] =
      MvPowerSeries.rescale ![0, 1] Φ := by sorry
