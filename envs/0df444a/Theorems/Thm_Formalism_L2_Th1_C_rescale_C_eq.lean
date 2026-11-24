-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_rescale_C_eq
-- name    : Formalism.L2.Th1.C.rescale_C_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:06.232923+00:00
-- url     : https://prove2.me/theorems/1fccf0da-9206-4114-ab52-b3890a58b0a7
-- title:
--   C: rescale C eq
-- statement:
--   The C construction uses the rescale C eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/HasSecondLogDerivPowerSeriesExp.lean#L150-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/HasSecondLogDerivPowerSeriesExp.lean#L150-L153

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

theorem Formalism.L2.Th1.C.rescale_C_eq (a b : K) : rescale a (C b : PowerSeries K) = C b := by sorry
