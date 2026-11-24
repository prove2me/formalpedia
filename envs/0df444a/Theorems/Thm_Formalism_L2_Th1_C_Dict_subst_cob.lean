-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Dict_subst_cob
-- name    : Formalism.L2.Th1.C.Dict.subst_cob
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:14.23878+00:00
-- url     : https://prove2.me/theorems/f51f19bf-604e-42a1-a627-6ae834b96b95
-- title:
--   Dict: subst cob
-- statement:
--   The Dict construction uses the subst cob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/ConstantCoeffVecConsPairEqZero.lean#L79-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/ConstantCoeffVecConsPairEqZero.lean#L79-L88

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

theorem Formalism.L2.Th1.C.Dict.subst_cob (h : IsLogPair l linv) (ph : PowerSeries K) {x y : MvPowerSeries τ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.subst ![x, y]
      (Formalism.InvariantFactorPaths.G7.cob (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) ph) =
      be0 l linv ph x y := by sorry
