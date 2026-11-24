-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_coeff_dq
-- name    : Formalism.L2.Th1.B.coeff_dq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:02.770582+00:00
-- url     : https://prove2.me/theorems/b0300380-807a-420a-a80d-a64808025d45
-- title:
--   B: coeff dq
-- statement:
--   The B construction uses the coeff dq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/EvalSecondZeroAtVariableZero.lean#L263-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/EvalSecondZeroAtVariableZero.lean#L263-L265

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

theorem Formalism.L2.Th1.B.coeff_dq {K : Type} [Field K] [CharZero K] (P : PowerSeries K) (n : Fin 2 →₀ ℕ) :
    coeff n (dq P) =
      if Even (n 0) ∧ Even (n 1) then PowerSeries.coeff (n 0 + n 1 + 2) P else 0 := by sorry
