-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_coeff_eq_zero_of_eval_second_zero
-- name    : Formalism.L2.Th1.B.coeff_eq_zero_of_eval_second_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:50.021138+00:00
-- url     : https://prove2.me/theorems/28c94396-afe1-455a-bc3e-bc84c6970c14
-- title:
--   B: coeff eq zero of eval second zero
-- statement:
--   The B construction uses the coeff eq zero of eval second zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/EvalSecondZeroAtVariableZero.lean#L136-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/EvalSecondZeroAtVariableZero.lean#L136-L141

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

theorem Formalism.L2.Th1.B.coeff_eq_zero_of_eval_second_zero {h : MvPowerSeries (Fin 2) K} (h0 : ev0 h = 0) (n : Fin 2 →₀ ℕ)
    (hn : n 1 = 0) : coeff n h = 0 := by sorry
