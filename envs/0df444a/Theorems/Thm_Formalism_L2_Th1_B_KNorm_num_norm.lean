-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_KNorm_num_norm
-- name    : Formalism.L2.Th1.B.KNorm.num_norm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:47:28.120784+00:00
-- url     : https://prove2.me/theorems/5c4403cd-a9ea-46e0-b6dd-c160704f7102
-- title:
--   KNorm: num norm
-- statement:
--   The KNorm construction uses the num norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L105-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L105-L116

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
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable {b2 b4 b6 b8 x : K}

theorem Formalism.L2.Th1.B.KNorm.num_norm (h2 : ‖(2 : K)‖ = 2⁻¹) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1) (hb8 : ‖b8‖ ≤ 1)
    (hx : 4 ≤ ‖x‖) : ‖x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8‖ = ‖x‖ ^ 4 := by sorry
