-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_derivative_mvExp
-- name    : Formalism.L2.Th1.C.derivative_mvExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:44.607774+00:00
-- url     : https://prove2.me/theorems/1edd22a5-1aa7-4be8-b632-59805b1d00fe
-- title:
--   C: derivative mv Exp
-- statement:
--   The C construction uses the derivative mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L268-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L268-L272

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] {σ : Type}

theorem Formalism.L2.Th1.C.derivative_mvExp {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.derivative K (mvExp f : PowerSeries K) =
      PowerSeries.derivative K f * (mvExp f : PowerSeries K) := by sorry
