-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_KNorm_b_int
-- name    : Formalism.L2.Th1.B.KNorm.b_int
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:45:27.576868+00:00
-- url     : https://prove2.me/theorems/fc22115e-50d7-4087-a88c-dda942760a0d
-- title:
--   KNorm: b int
-- statement:
--   The KNorm construction uses the b int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L57-L64

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

theorem Formalism.L2.Th1.B.KNorm.b_int (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) :
    ‖W.b₂‖ ≤ 1 ∧ ‖W.b₄‖ ≤ 1 ∧ ‖W.b₆‖ ≤ 1 ∧ ‖W.b₈‖ ≤ 1 := by sorry
