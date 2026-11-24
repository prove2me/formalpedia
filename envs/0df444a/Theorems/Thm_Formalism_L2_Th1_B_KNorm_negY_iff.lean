-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_KNorm_negY_iff
-- name    : Formalism.L2.Th1.B.KNorm.negY_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:44.493404+00:00
-- url     : https://prove2.me/theorems/44cecf68-cf79-4ca5-a72a-9385ba06cf2d
-- title:
--   KNorm: neg Y iff
-- statement:
--   The KNorm construction uses the neg Y iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L202-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L202-L204

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.KNorm
open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.E (px py IntCurve)
open WeierstrassCurve.Affine (Point)
variable {K : Type} [Field K] {W : WeierstrassCurve K} {x y : K}

theorem Formalism.L2.Th1.B.KNorm.negY_iff : y = W.toAffine.negY x y ↔ 2 * y + W.a₁ * x + W.a₃ = 0 := by sorry
