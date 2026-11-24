-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Scale_sgStar_scale
-- name    : Formalism.L2.Th1.F.Scale.sgStar_scale
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:20:14.171886+00:00
-- url     : https://prove2.me/theorems/27515eaf-2836-4d69-98aa-b88034a8b5ab
-- title:
--   Scale: sg Star scale
-- statement:
--   The Scale construction uses the sg Star scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaScale.lean#L147-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaScale.lean#L147-L163

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

theorem Formalism.L2.Th1.F.Scale.sgStar_scale (s lam : K) (P : PowerSeries K) :
    C lam * Formalism.L2.Th1.B.sgStar (lam ^ 2 * s) (C (lam ^ 2) * rescale lam P)
      = rescale lam (Formalism.L2.Th1.B.sgStar s P) := by sorry
