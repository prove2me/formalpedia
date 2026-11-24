-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_KNorm_px_add_self
-- name    : Formalism.L2.Th1.B.KNorm.px_add_self
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:47:34.092727+00:00
-- url     : https://prove2.me/theorems/3db1ff98-e024-415d-9899-f1f1103de821
-- title:
--   KNorm: px add self
-- statement:
--   The KNorm construction uses the px add self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L232-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/TwoTorsionKernelUniqueHolds.lean#L232-L236

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
variable [DecidableEq K]

theorem Formalism.L2.Th1.B.KNorm.px_add_self (h : W.toAffine.Nonsingular x y) (hy : y ≠ W.toAffine.negY x y) :
    px W (Point.some x y h + Point.some x y h)
      = W.toAffine.addX x x (W.toAffine.slope x x y y) := by sorry
