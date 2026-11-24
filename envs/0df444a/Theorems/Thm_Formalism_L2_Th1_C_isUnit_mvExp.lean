-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_isUnit_mvExp
-- name    : Formalism.L2.Th1.C.isUnit_mvExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:52.077985+00:00
-- url     : https://prove2.me/theorems/b102c535-1676-4ec8-ab1f-6bc8d2cb806e
-- title:
--   C: is Unit mv Exp
-- statement:
--   The C construction uses the is Unit mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L189-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L189-L190

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

theorem Formalism.L2.Th1.C.isUnit_mvExp {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    IsUnit (mvExp f) := by sorry
