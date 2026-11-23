-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_constantCoeff_rescale_eq
-- name    : Formalism.L2.Th1.C.constantCoeff_rescale_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:10.533808+00:00
-- url     : https://prove2.me/theorems/882476fc-c448-4382-a8dd-b5b2cc4a5171
-- title:
--   C: constant Coeff rescale eq
-- statement:
--   The C construction uses the constant Coeff rescale eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/HasSecondLogDerivPowerSeriesExp.lean#L155-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/HasSecondLogDerivPowerSeriesExp.lean#L155-L158

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ChordSecondLogDeriv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_HasSecondLogDerivPowerSeriesExp
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
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.C.constantCoeff_rescale_eq (a : K) (f : PowerSeries K) :
    constantCoeff (rescale a f) = constantCoeff f := by sorry
