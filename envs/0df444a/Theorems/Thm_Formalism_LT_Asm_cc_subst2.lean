-- Prove2me | Theorems.Thm_Formalism_LT_Asm_cc_subst2
-- name    : Formalism.LT.Asm.cc_subst2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:04.031188+00:00
-- url     : https://prove2.me/theorems/6f418d07-4bfe-490b-b8c6-144c38d8c2b3
-- title:
--   Asm: cc subst2
-- statement:
--   The Asm construction uses the cc subst2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L149-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L149-L157

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

theorem Formalism.LT.Asm.cc_subst2 {R : Type*} [CommRing R] {τ : Type*} [Finite τ] (F : MvPowerSeries (Fin 2) R)
    (hF0 : MvPowerSeries.constantCoeff F = 0) {u v : MvPowerSeries τ R}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    MvPowerSeries.constantCoeff (F.subst ![u, v]) = 0 := by sorry
