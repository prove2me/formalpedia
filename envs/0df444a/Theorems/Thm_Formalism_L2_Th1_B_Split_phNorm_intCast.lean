-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Split_phNorm_intCast
-- name    : Formalism.L2.Th1.B.Split.phNorm_intCast
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:01:08.806517+00:00
-- url     : https://prove2.me/theorems/a8a453f3-8c7d-44a8-8b8f-5335709dc7bd
-- title:
--   Split: ph Norm int Cast
-- statement:
--   The Split construction uses the ph Norm int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BiextensionFormalMulMul.lean#L82-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BiextensionFormalMulMul.lean#L82-L99

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BiextensionFormalMulMul
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_LT_InvIntP_key

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

theorem Formalism.L2.Th1.B.Split.phNorm_intCast (hF : Frame R l linv ph)
    (key : ∀ x y : MvPowerSeries Unit K, IsPt R x → IsPt R y → LG R (be0 l linv ph x y)) (n : ℤ) :
    PhNormAt R l linv ph (n : K) 1 := by sorry
