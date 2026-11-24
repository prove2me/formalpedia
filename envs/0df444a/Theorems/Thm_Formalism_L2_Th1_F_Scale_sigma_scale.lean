-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Scale_sigma_scale
-- name    : Formalism.L2.Th1.F.Scale.sigma_scale
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:20:38.551801+00:00
-- url     : https://prove2.me/theorems/d68c52c5-4df4-41f4-9a39-9be8608cc678
-- title:
--   Scale: sigma scale
-- statement:
--   The Scale construction uses the sigma scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaScale.lean#L140-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaScale.lean#L140-L145

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
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.F.Scale.sigma_scale (lam : K) (P : PowerSeries K) :
    C lam * Formalism.L2.Th1.B.sigma (C (lam ^ 2) * rescale lam P)
      = rescale lam (Formalism.L2.Th1.B.sigma P) := by sorry
