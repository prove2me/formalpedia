-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_pderiv_one_parallelogram_defect
-- name    : Formalism.L2.Th1.B.pderiv_one_parallelogram_defect
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:12.229916+00:00
-- url     : https://prove2.me/theorems/29f74503-fa98-432a-8695-5d2bddd89ff2
-- title:
--   B: pderiv one parallelogram defect
-- statement:
--   The B construction uses the pderiv one parallelogram defect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/EvalSecondZeroAtVariableZero.lean#L233-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/EvalSecondZeroAtVariableZero.lean#L233-L237

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

theorem Formalism.L2.Th1.B.pderiv_one_parallelogram_defect (f : PowerSeries K) :
    pd 1 (par0 f) = atS (dz f) - atD (dz f) - 2 * at1 1 (dz f) := by sorry
