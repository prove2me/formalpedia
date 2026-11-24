-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_KNorm_two_tors_le
-- name    : Formalism.L2.Th1.B.KNorm.two_tors_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:16.842086+00:00
-- url     : https://prove2.me/theorems/1899ea5a-5737-488d-9762-615eac1c1b8d
-- title:
--   KNorm: two tors le
-- statement:
--   The KNorm construction uses the two tors le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L245-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L245-L258

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

theorem Formalism.L2.Th1.B.KNorm.two_tors_le (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (P : W.toAffine.Point)
    (hP : P + P = 0) : ‖px W P‖ ≤ 4 := by sorry
