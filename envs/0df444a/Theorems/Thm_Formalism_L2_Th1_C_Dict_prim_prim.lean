-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Dict_prim_prim
-- name    : Formalism.L2.Th1.C.Dict.prim_prim
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:48.703801+00:00
-- url     : https://prove2.me/theorems/42c532b9-ee7d-4391-94d6-3dafab47b691
-- title:
--   Dict: prim prim
-- statement:
--   The Dict construction uses the prim prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/ConstantCoeffVecConsPairEqZero.lean#L126-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/ConstantCoeffVecConsPairEqZero.lean#L126-L138

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Dict
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.C.Dict.prim_prim (e : PowerSeries K) : Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim e) = dblInt e := by sorry
