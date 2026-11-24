-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Scale_uSer_map
-- name    : Formalism.L2.Th1.F.Scale.uSer_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:20:20.12118+00:00
-- url     : https://prove2.me/theorems/575c9530-7ee7-471a-ac13-609c8e08b3f1
-- title:
--   Scale: u Ser map
-- statement:
--   The Scale construction uses the u Ser map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaScale.lean#L206-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaScale.lean#L206-L210

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.Th1.CM (cW wpNum wpDen uSer)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Scale
open PowerSeries
variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem Formalism.L2.Th1.F.Scale.uSer_map [CharZero K] [CharZero K'] (g2 g3 : K) :
    map φ (uSer g2 g3) = uSer (φ g2) (φ g3) := by sorry
