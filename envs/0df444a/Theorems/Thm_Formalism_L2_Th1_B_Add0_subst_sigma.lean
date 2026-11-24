-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Add0_subst_sigma
-- name    : Formalism.L2.Th1.B.Add0.subst_sigma
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:17.202993+00:00
-- url     : https://prove2.me/theorems/1ad56857-015d-4fb7-83a7-7a36349517ac
-- title:
--   Add0: subst sigma
-- statement:
--   The Add0 construction uses the subst sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/PderivZeroZeroWeierstrassDifference.lean#L398-L404
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/PderivZeroZeroWeierstrassDifference.lean#L398-L404

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1)
open Add0
open Formalism.L2.Th1.B.Add0
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.Add0.subst_sigma (h3 : ExpLogSubst) (P : PowerSeries K) {u : MvPowerSeries (Fin 2) K}
    (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst u (sigma P) = u * fExp (PowerSeries.subst u (sigS P)) := by sorry
