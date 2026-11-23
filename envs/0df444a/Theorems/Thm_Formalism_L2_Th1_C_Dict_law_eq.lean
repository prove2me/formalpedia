-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Dict_law_eq
-- name    : Formalism.L2.Th1.C.Dict.law_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:55.709661+00:00
-- url     : https://prove2.me/theorems/d2531c7a-9ade-4327-9190-ccf6f027d61e
-- title:
--   Dict: law eq
-- statement:
--   The Dict construction uses the law eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/ConstantCoeffVecConsPairEqZero.lean#L110-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/ConstantCoeffVecConsPairEqZero.lean#L110-L118

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
variable {K : Type} [Field K] {σ τ : Type} {l linv : PowerSeries K}

theorem Formalism.L2.Th1.C.Dict.law_eq (h : IsLogPair l linv) {F : MvPowerSeries (Fin 2) K}
    (hF : MvPowerSeries.constantCoeff F = 0) (hc : Formalism.InvariantFactorPaths.G7.cob F l = 0) :
    F = fadd l linv (MvPowerSeries.X 0) (MvPowerSeries.X 1) := by sorry
