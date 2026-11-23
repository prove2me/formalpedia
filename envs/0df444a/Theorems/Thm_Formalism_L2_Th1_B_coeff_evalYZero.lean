-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_coeff_evalYZero
-- name    : Formalism.L2.Th1.B.coeff_evalYZero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:26.401863+00:00
-- url     : https://prove2.me/theorems/568e8f68-6620-454f-a17b-23f4a3f6680a
-- title:
--   B: coeff eval YZero
-- statement:
--   The B construction uses the coeff eval YZero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/EvalSecondZeroAtVariableZero.lean#L115-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/EvalSecondZeroAtVariableZero.lean#L115-L134

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

theorem Formalism.L2.Th1.B.coeff_evalYZero (h : MvPowerSeries (Fin 2) K) (k : ℕ) :
    PowerSeries.coeff k (ev0 h) = coeff (Finsupp.single 0 k) h := by sorry
