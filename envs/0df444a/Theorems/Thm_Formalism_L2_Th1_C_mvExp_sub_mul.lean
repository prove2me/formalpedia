-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_mvExp_sub_mul
-- name    : Formalism.L2.Th1.C.mvExp_sub_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:37.555512+00:00
-- url     : https://prove2.me/theorems/051c8fdd-6d5a-4da4-9341-eb3d7a74dedc
-- title:
--   C: mv Exp sub mul
-- statement:
--   The C construction uses the mv Exp sub mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L195-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L195-L197

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

theorem Formalism.L2.Th1.C.mvExp_sub_mul {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f - g) * mvExp g = mvExp f := by sorry
