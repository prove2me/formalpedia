-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Scale_uSer_scale
-- name    : Formalism.L2.Th1.F.Scale.uSer_scale
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:20:00.828048+00:00
-- url     : https://prove2.me/theorems/7f7b162f-be91-411d-8642-d113216bee25
-- title:
--   Scale: u Ser scale
-- statement:
--   The Scale construction uses the u Ser scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaScale.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaScale.lean#L104-L109

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

theorem Formalism.L2.Th1.F.Scale.uSer_scale {K : Type} [Field K] (g2 g3 lam : K) :
    C lam * uSer (lam ^ 4 * g2) (lam ^ 6 * g3) = rescale lam (uSer g2 g3) := by sorry
