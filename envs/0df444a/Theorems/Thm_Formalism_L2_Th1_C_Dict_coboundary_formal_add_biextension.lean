-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Dict_coboundary_formal_add_biextension
-- name    : Formalism.L2.Th1.C.Dict.coboundary_formal_add_biextension
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:36.470293+00:00
-- url     : https://prove2.me/theorems/7483fa77-7e16-436b-ae47-bc58abec72b3
-- title:
--   Dict: coboundary formal add biextension
-- statement:
--   The Dict construction uses the coboundary formal add biextension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/ConstantCoeffVecConsPairEqZero.lean#L90-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/ConstantCoeffVecConsPairEqZero.lean#L90-L108

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

theorem Formalism.L2.Th1.C.Dict.coboundary_formal_add_biextension (h : IsLogPair l linv) (ph : PowerSeries K) :
    Formalism.InvariantFactorPaths.G7.d1 (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)))
      (Formalism.InvariantFactorPaths.G7.cob (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) ph) =
      be0 l linv ph (fadd l linv (MvPowerSeries.X (0 : Fin 3)) (MvPowerSeries.X (1 : Fin 3)))
          (MvPowerSeries.X (2 : Fin 3)) -
        be0 l linv ph (MvPowerSeries.X (0 : Fin 3)) (MvPowerSeries.X (2 : Fin 3)) -
        be0 l linv ph (MvPowerSeries.X (1 : Fin 3)) (MvPowerSeries.X (2 : Fin 3)) := by sorry
