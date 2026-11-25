-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Split_lg_of_smul
-- name    : Formalism.L2.Th1.B.Split.lg_of_smul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:31:32.246419+00:00
-- url     : https://prove2.me/theorems/19b0d608-bed8-5c14-b46e-07a4099d2cdc
-- title:
--   Split: lg of smul
-- statement:
--   The Split construction uses the lg of smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BiextensionFormalMulMul.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BiextensionFormalMulMul.lean#L19-L22

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BiextensionFormalMulMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Split
open Formalism.L2.Th1.C Formalism.L2.Th1.C.Pts Formalism.L2.Th1.C.Calc
variable {K : Type} [Field K] [CharZero K] {R : Subring K} {l linv ph : PowerSeries K}

theorem Formalism.L2.Th1.B.Split.lg_of_smul {σ : Type} {c : K} (hc : c ≠ 0) (hz : IsBinomScalar R c⁻¹)
    {f : MvPowerSeries σ K} (h : LG R (c • f)) : LG R f := by sorry
