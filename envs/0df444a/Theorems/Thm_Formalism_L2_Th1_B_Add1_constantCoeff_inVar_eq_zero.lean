-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Add1_constantCoeff_inVar_eq_zero
-- name    : Formalism.L2.Th1.B.Add1.constantCoeff_inVar_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:30.454852+00:00
-- url     : https://prove2.me/theorems/6dccbda8-bfff-4623-99b2-843eed0db1bb
-- title:
--   Add1: constant Coeff in Var eq zero
-- statement:
--   The Add1 construction uses the constant Coeff in Var eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RestrictSecondZeroInVarOne.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RestrictSecondZeroInVarOne.lean#L41-L43

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RestrictSecondZeroInVarOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Add1
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.Add1.constantCoeff_inVar_eq_zero {ι : Type} (x : ι) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (at1 x f) = 0 := by sorry
