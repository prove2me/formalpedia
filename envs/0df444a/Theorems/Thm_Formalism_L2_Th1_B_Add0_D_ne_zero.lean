-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Add0_D_ne_zero
-- name    : Formalism.L2.Th1.B.Add0.D_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:44.907324+00:00
-- url     : https://prove2.me/theorems/9c990a78-3f00-4d55-af5d-6da2b1d382b9
-- title:
--   Add0: D ne zero
-- statement:
--   The Add0 construction uses the D ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/PderivZeroZeroWeierstrassDifference.lean#L254-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/PderivZeroZeroWeierstrassDifference.lean#L254-L261

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
open Formalism.L2.Th1.B.Add0
variable {K : Type} [Field K] [CharZero K]
local notation "A2" => MvPowerSeries (Fin 2) K

theorem Formalism.L2.Th1.B.Add0.D_ne_zero : (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2 : A2) ≠ 0 := by sorry
