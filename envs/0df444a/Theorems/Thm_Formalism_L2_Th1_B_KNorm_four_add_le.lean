-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_KNorm_four_add_le
-- name    : Formalism.L2.Th1.B.KNorm.four_add_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:46:53.597696+00:00
-- url     : https://prove2.me/theorems/5958bb57-8b31-4551-89b0-e64a2686ee9e
-- title:
--   KNorm: four add le
-- statement:
--   The KNorm construction uses the four add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L150-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L150-L158

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

theorem Formalism.L2.Th1.B.KNorm.four_add_le (h2 : ‖(2 : K)‖ = 2⁻¹) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hx : ‖x‖ = 4) (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0) :
    ‖4 * x + b2‖ ≤ 1 / 8 := by sorry
