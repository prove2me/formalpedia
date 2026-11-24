-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_KNorm_dup_big
-- name    : Formalism.L2.Th1.B.KNorm.dup_big
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:46:57.165098+00:00
-- url     : https://prove2.me/theorems/46d701a3-8f34-4494-8284-5f952e4a2223
-- title:
--   KNorm: dup big
-- statement:
--   The KNorm construction uses the dup big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L260-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L260-L272

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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [DecidableEq K]
  {W : WeierstrassCurve K}

theorem Formalism.L2.Th1.B.KNorm.dup_big (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (P : W.toAffine.Point)
    (hx : 4 ≤ ‖px W P‖) (hP : P + P ≠ 0) : 4 < ‖px W (P + P)‖ := by sorry
