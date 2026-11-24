-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Dict_cob_eq
-- name    : Formalism.L2.Th1.C.Dict.cob_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:28.268963+00:00
-- url     : https://prove2.me/theorems/b45d1958-c8dc-4c9b-920a-669445d9edda
-- title:
--   Dict: cob eq
-- statement:
--   The Dict construction uses the cob eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/ConstantCoeffVecConsPairEqZero.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/ConstantCoeffVecConsPairEqZero.lean#L75-L77

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

theorem Formalism.L2.Th1.C.Dict.cob_eq (ph : PowerSeries K) :
    Formalism.InvariantFactorPaths.G7.cob (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) ph =
      be0 l linv ph (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)) := by sorry
