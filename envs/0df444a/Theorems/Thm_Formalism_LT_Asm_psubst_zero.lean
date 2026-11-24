-- Prove2me | Theorems.Thm_Formalism_LT_Asm_psubst_zero
-- name    : Formalism.LT.Asm.psubst_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:51:16.969568+00:00
-- url     : https://prove2.me/theorems/d5cd1bd0-f796-489b-af0e-36f5a2417c91
-- title:
--   Asm: psubst zero
-- statement:
--   The Asm construction uses the psubst zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L134-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L134-L139

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

theorem Formalism.LT.Asm.psubst_zero {R : Type*} [CommRing R] {τ : Type*} (f : PowerSeries R)
    (hf0 : constantCoeff f = 0) : f.subst (0 : MvPowerSeries τ R) = 0 := by sorry
