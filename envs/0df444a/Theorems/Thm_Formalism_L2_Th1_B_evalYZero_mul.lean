-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_evalYZero_mul
-- name    : Formalism.L2.Th1.B.evalYZero_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:31.048868+00:00
-- url     : https://prove2.me/theorems/1e27e7d1-0536-4b5f-b8c9-5949855c160a
-- title:
--   B: eval YZero mul
-- statement:
--   The B construction uses the eval YZero mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/EvalSecondZeroAtVariableZero.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/EvalSecondZeroAtVariableZero.lean#L41-L42

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_single_variable_series

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
open Formalism.InvariantFactorPaths.G7 (at1 coeff_single_variable_series)
open MvPowerSeries (coeff constantCoeff)
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.evalYZero_mul (g h : MvPowerSeries (Fin 2) K) : ev0 (g * h) = ev0 g * ev0 h := by sorry
