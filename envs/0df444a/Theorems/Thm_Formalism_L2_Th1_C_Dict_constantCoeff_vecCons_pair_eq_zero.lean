-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Dict_constantCoeff_vecCons_pair_eq_zero
-- name    : Formalism.L2.Th1.C.Dict.constantCoeff_vecCons_pair_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:56.581794+00:00
-- url     : https://prove2.me/theorems/62409bd3-f00a-4755-b61a-d3541612f14b
-- title:
--   Dict: constant Coeff vec Cons pair eq zero
-- statement:
--   The Dict construction uses the constant Coeff vec Cons pair eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/ConstantCoeffVecConsPairEqZero.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/ConstantCoeffVecConsPairEqZero.lean#L58-L64

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

theorem Formalism.L2.Th1.C.Dict.constantCoeff_vecCons_pair_eq_zero {x y : MvPowerSeries τ K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    ∀ s : Fin 2, MvPowerSeries.constantCoeff (![x, y] s) = 0 := by sorry
