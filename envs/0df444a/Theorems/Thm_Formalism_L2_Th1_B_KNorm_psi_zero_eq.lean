-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_KNorm_psi_zero_eq
-- name    : Formalism.L2.Th1.B.KNorm.psi_zero_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:47:17.084313+00:00
-- url     : https://prove2.me/theorems/3454aa8b-a61d-4b21-bf0a-09f27c967d92
-- title:
--   KNorm: psi zero eq
-- statement:
--   The KNorm construction uses the psi zero eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L133-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L133-L148

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

theorem Formalism.L2.Th1.B.KNorm.psi_zero_eq (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ = 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hx : 1 < ‖x‖) (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0) : ‖x‖ = 4 := by sorry
