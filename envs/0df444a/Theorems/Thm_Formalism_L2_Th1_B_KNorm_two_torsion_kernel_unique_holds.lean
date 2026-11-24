-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_KNorm_two_torsion_kernel_unique_holds
-- name    : Formalism.L2.Th1.B.KNorm.two_torsion_kernel_unique_holds
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:03.055804+00:00
-- url     : https://prove2.me/theorems/04a87e1d-573f-4196-be99-baf19b9b65cd
-- title:
--   KNorm: two torsion kernel unique holds
-- statement:
--   The KNorm construction uses the two torsion kernel unique holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L348-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L348-L350

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
open Classical

theorem Formalism.L2.Th1.B.KNorm.two_torsion_kernel_unique_holds : TwoTorsionKernelUnique := by sorry
